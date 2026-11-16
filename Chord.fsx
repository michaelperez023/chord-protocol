// Chord peer-to-peer lookup protocol (Stoica et al., SIGCOMM 2001) with one Akka.NET actor per peer.
// Authors: Blas Kojusner and Michael Perez - COP 5615 Distributed Operating System Principles - Project 3
//
// Usage: dotnet fsi Chord.fsx <numNodes> <numRequests> [--verify] [--seed <n>]
//   numNodes     number of peers; about a tenth of them join through the protocol
//   numRequests  lookups per peer, one per second
//   --verify     check that every lookup ended at the successor of its key (exit code 1 if not)
//   --seed <n>   seed for the lookup keys, to repeat a run

#r "nuget: Akka.FSharp, 1.5.74"

open System
open System.Collections.Generic
open System.Diagnostics
open System.Numerics
open System.Security.Cryptography
open System.Text
open System.Threading.Tasks
open Akka.Actor
open Akka.FSharp

// ---------------------------------------------------------------------------
// Identifiers

/// Smallest b with 2^b >= n.
let ceilLog2 (n: int) =
    let mutable b = 0
    while (1L <<< b) < int64 n do
        b <- b + 1
    b

/// m-bit identifier: the SHA-1 digest of the text read as an unsigned number, mod 2^m.
let chordId (ringSize: bigint) (text: string) =
    let digest = SHA1.HashData(Encoding.UTF8.GetBytes text)
    BigInteger(ReadOnlySpan<byte>(digest), isUnsigned = true, isBigEndian = true) % ringSize

/// x is in the ring interval (a, b). When a = b this is every identifier except a.
let inOpen (a: bigint) (b: bigint) (x: bigint) =
    if a < b then a < x && x < b
    elif a > b then a < x || x < b
    else x <> a

/// x is in the ring interval (a, b]. When a = b this is the whole ring.
let inHalfOpen (a: bigint) (b: bigint) (x: bigint) =
    if a < b then a < x && x <= b
    elif a > b then a < x || x <= b
    else true

let randomText (random: Random) length =
    let chars = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"
    String(Array.init length (fun _ -> chars.[random.Next chars.Length]))

// ---------------------------------------------------------------------------
// Messages

/// A peer as other peers know it: its identifier and its actor (its address).
type NodeRef = { Id: bigint; Ref: IActorRef }

/// Why a find_successor request was sent.
type Purpose =
    | Lookup of text: string // a peer looking up the key of a string; its hops are counted
    | JoinRing // a new peer looking for its successor
    | FixFinger of int // a peer refreshing finger i

type FindRequest =
    { Key: bigint
      Requester: NodeRef
      Purpose: Purpose
      Hops: int }

type LookupResult = { Key: bigint; Owner: bigint; Hops: int }

type NodeConfig =
    { Id: bigint
      Bits: int // m: identifiers are m-bit numbers
      SuccessorListSize: int
      NumRequests: int
      Tick: TimeSpan // period of stabilize and fix_fingers while the ring forms
      Seed: int
      Boss: IActorRef }

/// The routing state of a peer, as the boss checks it.
type NodeView =
    { Id: bigint
      Successor: bigint
      Predecessor: bigint option
      Fingers: bigint list
      Successors: bigint list }

type Message =
    // boss
    | BossStart
    | PollRing
    | NodeState of round: int * NodeView
    | Complete of LookupResult list
    | LookupCheck
    // boss to peer
    | Initialize of predecessor: NodeRef * fingers: NodeRef list * successors: NodeRef list
    | Join of bootstrap: NodeRef
    | GetState of round: int
    | NodeStart
    // timers of a peer
    | Stabilize
    | FixFingers
    | SendRequest
    // between peers
    | StabilizeAskSuccessor of asker: NodeRef
    | StabilizeSuccessorSendPredecessor of replier: NodeRef * predecessor: NodeRef option * successors: NodeRef list
    | StabilizeNotify of NodeRef
    | FindSuccessor of FindRequest
    | Deliver of FindRequest
    | SuccessorFound of FindRequest * owner: NodeRef * ownerSuccessors: NodeRef list

// ---------------------------------------------------------------------------
// Routing

type Route =
    | Here // this peer is the successor of the key
    | Successor of NodeRef // the key lies between this peer and its successor
    | Closer of NodeRef // forward to the closest preceding peer this peer knows

/// One step of find_successor(key) at peer self.
let decideDestination
    (key: bigint)
    (self: NodeRef)
    (predecessor: NodeRef option)
    (successor: NodeRef)
    (fingers: NodeRef[])
    (successors: NodeRef list)
    =
    let ownsKey =
        match predecessor with
        | Some p -> inHalfOpen p.Id self.Id key
        | None -> successor.Id = self.Id

    if ownsKey then
        Here
    elif inHalfOpen self.Id successor.Id key then
        Successor successor
    else
        // closest_preceding_node: of the fingers and the successor list, the peer in (self, key) nearest to key
        let mutable best = successor

        for candidate in Seq.append fingers successors do
            if inOpen self.Id key candidate.Id && inOpen best.Id key candidate.Id then
                best <- candidate

        Closer best

// ---------------------------------------------------------------------------
// Peer

let NodeActor (config: NodeConfig) (mailbox: Actor<Message>) =
    let self: NodeRef = { Id = config.Id; Ref = mailbox.Self }
    let ringSize = BigInteger.Pow(2I, config.Bits)
    // finger i points to successor((n + 2^i) mod 2^m)
    let fingerStart =
        Array.init config.Bits (fun i -> (config.Id + BigInteger.Pow(2I, i)) % ringSize)

    let keys = Random(config.Seed)

    let mutable predecessor: NodeRef option = None
    let mutable successor = self
    let fingers = Array.create config.Bits self
    let mutable successors: NodeRef list = []
    let mutable nextFinger = 0
    let mutable period = config.Tick // of stabilize and fix_fingers; once a second during the lookups
    let mutable requestsSent = 0
    let mutable results: LookupResult list = []

    let schedule (delay: TimeSpan) message =
        mailbox.Context.System.Scheduler.ScheduleTellOnce(delay, mailbox.Self, message)
        |> ignore

    /// Successor list: the given peers in ring order, without this peer or repeats, at most r of them.
    let successorList (peers: NodeRef list) =
        peers
        |> List.filter (fun p -> p.Id <> self.Id)
        |> List.distinctBy (fun p -> p.Id)
        |> List.truncate config.SuccessorListSize

    let answer (request: FindRequest) =
        request.Requester.Ref <! SuccessorFound(request, self, successors)

    let route (request: FindRequest) =
        match decideDestination request.Key self predecessor successor fingers successors with
        | Here -> answer request
        | Successor next -> next.Ref <! Deliver { request with Hops = request.Hops + 1 }
        | Closer next -> next.Ref <! FindSuccessor { request with Hops = request.Hops + 1 }

    /// stabilize and fix_fingers each schedule their next run when they run, so a busy peer never queues
    /// more than one of each. The first run is at a random point in the period so that peers are not in step.
    let startMaintenance () =
        let phase =
            TimeSpan.FromMilliseconds(Random.Shared.NextDouble() * period.TotalMilliseconds)

        schedule phase Stabilize
        schedule (phase + period / 2.0) FixFingers

    /// stabilize, second half: x is the successor's predecessor. If x is in (n, successor), x joined in
    /// between and becomes the successor. Then copy the successor list and notify the successor.
    /// A late reply from a peer that is no longer the successor is ignored.
    let onSuccessorReply (replier: NodeRef) (x: NodeRef option) (replierSuccessors: NodeRef list) =
        if replier.Id = successor.Id then
            let newSuccessor =
                match x with
                | Some x when inOpen self.Id successor.Id x.Id -> x
                | _ -> successor

            successors <- successorList (newSuccessor :: replier :: replierSuccessors)
            successor <- newSuccessor
            fingers.[0] <- newSuccessor
            newSuccessor.Ref <! StabilizeNotify self

    /// notify(n'): n' thinks it might be this peer's predecessor.
    let notify (candidate: NodeRef) =
        let closer =
            match predecessor with
            | None -> true
            | Some p -> inOpen p.Id self.Id candidate.Id

        if closer then
            predecessor <- Some candidate

    /// fix_fingers: refresh the next finger. Finger 0 is the successor, which stabilize keeps up to date.
    let fixFingers () =
        if config.Bits > 1 then
            nextFinger <- if nextFinger + 1 < config.Bits then nextFinger + 1 else 1
            let start = fingerStart.[nextFinger]

            if inHalfOpen self.Id successor.Id start then
                fingers.[nextFinger] <- successor
            else
                route
                    { Key = start
                      Requester = self
                      Purpose = FixFinger nextFinger
                      Hops = 0 }

    let onSuccessorFound (request: FindRequest) (owner: NodeRef) (ownerSuccessors: NodeRef list) =
        match request.Purpose with
        | JoinRing ->
            successor <- owner
            Array.fill fingers 0 fingers.Length owner
            successors <- successorList (owner :: ownerSuccessors)
            startMaintenance ()
        | FixFinger i -> fingers.[i] <- owner
        | Lookup _ ->
            let result: LookupResult =
                { Key = request.Key
                  Owner = owner.Id
                  Hops = request.Hops }

            results <- result :: results

            if List.length results = config.NumRequests then
                config.Boss <! Complete results

    let sendRequest () =
        if requestsSent < config.NumRequests then
            requestsSent <- requestsSent + 1
            let text = randomText keys 5

            route
                { Key = chordId ringSize text
                  Requester = self
                  Purpose = Lookup text
                  Hops = 0 }

            if requestsSent < config.NumRequests then
                schedule (TimeSpan.FromSeconds 1.0) SendRequest

    let view () : NodeView =
        { Id = self.Id
          Successor = successor.Id
          Predecessor = predecessor |> Option.map (fun p -> p.Id)
          Fingers = fingers |> Array.map (fun f -> f.Id) |> List.ofArray
          Successors = successors |> List.map (fun s -> s.Id) }

    let handle message =
        match message with
        | Initialize(pred, fingerList, succList) ->
            // a member of the ring that the boss built
            predecessor <- Some pred
            fingerList |> List.iteri (fun i f -> fingers.[i] <- f)
            successor <- fingers.[0]
            successors <- succList
            startMaintenance ()
        | Join bootstrap ->
            // join(n'): predecessor = nil; successor = n'.find_successor(n)
            bootstrap.Ref
            <! FindSuccessor
                { Key = self.Id
                  Requester = self
                  Purpose = JoinRing
                  Hops = 0 }
        | Stabilize ->
            // stabilize, first half: ask the successor for its predecessor
            successor.Ref <! StabilizeAskSuccessor self
            schedule period Stabilize
        | StabilizeAskSuccessor asker -> asker.Ref <! StabilizeSuccessorSendPredecessor(self, predecessor, successors)
        | StabilizeSuccessorSendPredecessor(replier, x, replierSuccessors) -> onSuccessorReply replier x replierSuccessors
        | StabilizeNotify candidate -> notify candidate
        | FixFingers ->
            fixFingers ()
            schedule period FixFingers
        | FindSuccessor request -> route request
        | Deliver request -> answer request // the previous peer found that this peer is the key's successor
        | SuccessorFound(request, owner, ownerSuccessors) -> onSuccessorFound request owner ownerSuccessors
        | NodeStart ->
            // The ring is stable: keep maintaining it, but only once a second. The first request goes out
            // at a random time within the next second, then one per second.
            period <- TimeSpan.FromSeconds 1.0
            schedule (TimeSpan.FromMilliseconds(Random.Shared.NextDouble() * 1000.0)) SendRequest
        | SendRequest -> sendRequest ()
        | GetState round -> config.Boss <! NodeState(round, view ())
        | _ -> ()

    let rec loop () =
        actor {
            let! message = mailbox.Receive()
            handle message
            return! loop ()
        }

    loop ()

// ---------------------------------------------------------------------------
// Boss: builds the network, waits until the ring is stable, then collects the lookups

let BossActor
    (numNodes: int)
    (numRequests: int)
    (verify: bool)
    (seed: int)
    (finished: TaskCompletionSource<int>)
    (mailbox: Actor<Message>)
    =
    let clock = Stopwatch.StartNew()
    let random = Random(seed)

    // About a tenth of the peers join through the protocol; the others form the initial ring.
    let numJoining = if numNodes >= 2 then max 1 (numNodes / 10) else 0
    let numInitial = numNodes - numJoining
    let successorListSize = max 1 (ceilLog2 numNodes)
    let names = Array.init numNodes (fun i -> sprintf "peer%d" (i + 1))

    // m = 3 * ceil(log2 N) bits, one more at a time while two peers would share an identifier.
    let bits, ids =
        let rec pick m =
            let ids = names |> Array.map (chordId (BigInteger.Pow(2I, m)))

            if (Array.distinct ids).Length = numNodes then m, ids else pick (m + 1)

        pick (3 * max 1 (ceilLog2 numNodes))

    let ringSize = BigInteger.Pow(2I, bits)
    // While the ring forms, stabilize and fix_fingers run every 50 ms, less often in large networks.
    let tick = TimeSpan.FromMilliseconds(max 50.0 (float numNodes / 100.0))
    let pollEvery = TimeSpan.FromMilliseconds(max 250.0 (2.0 * tick.TotalMilliseconds))
    // The ring has stopped converging when this many polls in a row find no fewer wrong entries than the best poll
    // so far: at least 20, and enough for three rounds of fix_fingers. On a slow or busy machine each poll takes
    // longer, so the wait grows with it; there is no fixed limit on the total time.
    let stallPolls =
        max 20 (int (ceil (3.0 * float bits * tick.TotalMilliseconds / pollEvery.TotalMilliseconds)))

    /// The peer responsible for key in a ring sorted by identifier: the first peer at or after key.
    let successorOf (ring: NodeRef[]) (key: bigint) =
        let mutable lo = 0
        let mutable hi = ring.Length

        while lo < hi do
            let mid = (lo + hi) / 2

            if ring.[mid].Id < key then lo <- mid + 1 else hi <- mid

        if lo = ring.Length then ring.[0] else ring.[lo]

    /// Correct predecessor, fingers and successor list of the peer at position k of a sorted ring.
    let neighbours (ring: NodeRef[]) k =
        let n = ring.Length
        let id = ring.[k].Id
        let predecessor = ring.[(k + n - 1) % n]

        let fingers =
            List.init bits (fun i -> successorOf ring ((id + BigInteger.Pow(2I, i)) % ringSize))

        let successors = List.init (min successorListSize (n - 1)) (fun j -> ring.[(k + j + 1) % n])
        predecessor, fingers, successors

    /// The number of routing entries (successor, predecessor, fingers, successor list) in which two states differ.
    let differences (state: NodeView) (correct: NodeView) =
        let rec count (xs: bigint list) (ys: bigint list) acc =
            match xs, ys with
            | x :: xs, y :: ys -> count xs ys (if x = y then acc else acc + 1)
            | rest, []
            | [], rest -> acc + List.length rest

        (if state.Successor = correct.Successor then 0 else 1)
        + (if state.Predecessor = correct.Predecessor then 0 else 1)
        + count state.Fingers correct.Fingers 0
        + count state.Successors correct.Successors 0

    let mutable ring: NodeRef[] = [||] // every peer, sorted by identifier
    let expected = Dictionary<bigint, NodeView>() // the state of each peer once the ring is stable
    let mutable stabilizeStart = TimeSpan.Zero
    let mutable lookupStart = TimeSpan.Zero
    let mutable round = 0
    let mutable replies = 0
    let mutable unstable = 0 // peers with a wrong entry, in this poll
    let mutable wrongEntries = 0 // wrong entries over all peers, in this poll
    let mutable fewestWrong = Int32.MaxValue // the fewest wrong entries of any poll so far
    let mutable pollsWithoutProgress = 0
    let mutable checkEvery = TimeSpan.Zero // wait between two LookupCheck messages
    let mutable reportedAtCheck = 0 // peers that had reported their lookups at the last LookupCheck
    let mutable completed = 0
    let mutable lookups = 0
    let mutable totalHops = 0L
    let mutable maxHops = 0
    let mutable wrong: LookupResult list = []

    let schedule (delay: TimeSpan) message =
        mailbox.Context.System.Scheduler.ScheduleTellOnce(delay, mailbox.Self, message)
        |> ignore

    let start () =
        printfn
            "Chord: %d peers (%d in the initial ring, %d joining), %d requests each"
            numNodes
            numInitial
            numJoining
            numRequests

        printfn
            "m = %d bits, successor lists of %d, stabilize and fix_fingers every %g ms (1 s during lookups), seed %d"
            bits
            successorListSize
            tick.TotalMilliseconds
            seed

        let peers =
            Array.init numNodes (fun i ->
                let config: NodeConfig =
                    { Id = ids.[i]
                      Bits = bits
                      SuccessorListSize = successorListSize
                      NumRequests = numRequests
                      Tick = tick
                      Seed = seed + i
                      Boss = mailbox.Self }

                let peer: NodeRef =
                    { Id = ids.[i]
                      Ref = spawn mailbox names.[i] (NodeActor config) }

                peer)

        ring <- Array.sortBy (fun (p: NodeRef) -> p.Id) peers

        for k in 0 .. numNodes - 1 do
            let predecessor, fingers, successors = neighbours ring k

            let state: NodeView =
                { Id = ring.[k].Id
                  Successor = ring.[(k + 1) % numNodes].Id
                  Predecessor = Some predecessor.Id
                  Fingers = fingers |> List.map (fun f -> f.Id)
                  Successors = successors |> List.map (fun s -> s.Id) }

            expected.[state.Id] <- state

        // The first peers start as a correct ring ...
        let initial = Array.sortBy (fun (p: NodeRef) -> p.Id) peers.[.. numInitial - 1]

        for k in 0 .. numInitial - 1 do
            let predecessor, fingers, successors = neighbours initial k
            initial.[k].Ref <! Initialize(predecessor, fingers, successors)

        // ... and the others join through a random one of them.
        for joiner in peers.[numInitial ..] do
            joiner.Ref <! Join initial.[random.Next numInitial]

        stabilizeStart <- clock.Elapsed
        schedule pollEvery PollRing

    let poll () =
        round <- round + 1
        replies <- 0
        unstable <- 0
        wrongEntries <- 0

        for peer in ring do
            peer.Ref <! GetState round

    let onState r (state: NodeView) =
        if r = round then
            replies <- replies + 1
            let mismatches = differences state expected.[state.Id]

            if mismatches > 0 then
                unstable <- unstable + 1
                wrongEntries <- wrongEntries + mismatches

            if replies = numNodes then
                let elapsed = clock.Elapsed - stabilizeStart

                if unstable = 0 then
                    printfn
                        "Ring stable after %.1f s: every successor, predecessor, finger and successor list is correct"
                        elapsed.TotalSeconds

                    lookupStart <- clock.Elapsed

                    for peer in ring do
                        peer.Ref <! NodeStart

                    // Check for new reports every minute plus the time the ring took to form (longer on a slow or
                    // busy machine), starting that long after the last requests are due.
                    checkEvery <- TimeSpan.FromSeconds 60.0 + elapsed
                    schedule (TimeSpan.FromSeconds(float numRequests) + checkEvery) LookupCheck
                else
                    if wrongEntries < fewestWrong then
                        fewestWrong <- wrongEntries
                        pollsWithoutProgress <- 0
                    else
                        pollsWithoutProgress <- pollsWithoutProgress + 1

                    if pollsWithoutProgress < stallPolls then
                        schedule pollEvery PollRing
                    else
                        printfn
                            "Ring not stable after %.0f s: %d of %d peers have wrong entries, no improvement in %d polls"
                            elapsed.TotalSeconds
                            unstable
                            numNodes
                            stallPolls

                        finished.TrySetResult 1 |> ignore

    /// The boss checks that more peers have reported since the last check. If none has, some lookups never
    /// finished, and the program stops.
    let onLookupCheck () =
        if completed < numNodes then
            if completed > reportedAtCheck then
                reportedAtCheck <- completed
                schedule checkEvery LookupCheck
            else
                printfn
                    "Lookups: %d of %d peers had not reported after %.0f s, and none reported in the last %.0f s"
                    (numNodes - completed)
                    numNodes
                    (clock.Elapsed - lookupStart).TotalSeconds
                    checkEvery.TotalSeconds

                finished.TrySetResult 1 |> ignore

    let onComplete (results: LookupResult list) =
        completed <- completed + 1

        for result in results do
            lookups <- lookups + 1
            totalHops <- totalHops + int64 result.Hops
            maxHops <- max maxHops result.Hops

            if verify && result.Owner <> (successorOf ring result.Key).Id then
                wrong <- result :: wrong

        if completed = numNodes then
            printfn "Lookups: %d in %.1f s" lookups (clock.Elapsed - lookupStart).TotalSeconds

            printfn
                "Average hops per lookup: %.3f (max %d); 0.5 * log2(N) = %.3f"
                (float totalHops / float lookups)
                maxHops
                (0.5 * Math.Log2(float numNodes))

            if verify then
                if List.isEmpty wrong then
                    printfn "Verify: all %d lookups ended at the successor of their key" lookups
                else
                    printfn "Verify: %d of %d lookups ended at the wrong peer, for example:" (List.length wrong) lookups

                    for w in List.truncate 5 wrong do
                        printfn "  key %O reached %O, its successor is %O" w.Key w.Owner (successorOf ring w.Key).Id

            finished.TrySetResult(if verify && not (List.isEmpty wrong) then 1 else 0)
            |> ignore

    let rec loop () =
        actor {
            let! message = mailbox.Receive()

            match message with
            | BossStart -> start ()
            | PollRing -> poll ()
            | NodeState(r, state) -> onState r state
            | Complete results -> onComplete results
            | LookupCheck -> onLookupCheck ()
            | _ -> ()

            return! loop ()
        }

    loop ()

// ---------------------------------------------------------------------------
// Main

let usage =
    "usage: dotnet fsi Chord.fsx <numNodes> <numRequests> [--verify] [--seed <n>]"

let tryInt (text: string) =
    match Int32.TryParse text with
    | true, value -> Some value
    | _ -> None

let rec parseOptions verify seed args =
    match args with
    | [] -> Some(verify, seed)
    | "--verify" :: rest -> parseOptions true seed rest
    | "--seed" :: value :: rest when (tryInt value).IsSome -> parseOptions verify (tryInt value) rest
    | _ -> None

let parseArguments (args: string list) =
    match args with
    | nodes :: requests :: options ->
        (match tryInt nodes, tryInt requests, parseOptions false None options with
         | Some n, Some r, Some(verify, seed) when n >= 1 && r >= 1 -> Some(n, r, verify, seed)
         | _ -> None)
    | _ -> None

match parseArguments (List.tail (List.ofArray fsi.CommandLineArgs)) with
| None ->
    eprintfn "%s" usage
    exit 2
| Some(numNodes, numRequests, verify, seed) ->
    let seed = defaultArg seed (Random.Shared.Next())

    let config =
        Akka.Configuration.ConfigurationFactory.ParseString
            """
            akka {
                loglevel = WARNING
                log-dead-letters = off
                log-dead-letters-during-shutdown = off
            }
            """

    let system = ActorSystem.Create("chord", config)
    let finished = TaskCompletionSource<int>()
    let boss = spawn system "boss" (BossActor numNodes numRequests verify seed finished)
    boss <! BossStart
    let code = finished.Task.Result
    system.Terminate().Wait()
    exit code
