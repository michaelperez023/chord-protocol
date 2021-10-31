// Authors: Blas Kojusner and Michael Perez - UFID: 62498470 - Distributed Operating Systems - COP5615 - Project3
#r "nuget: Akka.FSharp"

open System
open Akka.Actor
open Akka.FSharp
open System.Text
open System.Security.Cryptography

let system = ActorSystem.Create("System")
let timer = System.Diagnostics.Stopwatch()
let r = System.Random()

type Message =
    | Start
    | Join of int*IActorRef
    | UpdateFingerTable of Map<int, IActorRef>*Map<int,int>
    | UpdateSuccessors
    | RequestFingerTables of IActorRef
    | NodeAddComplete of int
    | SetRequests of int
    | SetFingerTable of Map<int,IActorRef>*Map<int,int>
    | StartRequesting
    | SendRequest
    | Request of IActorRef*int
    | Receipt
    | RequestFwd of int*IActorRef*int

let ranStr n = 
    let r = Random()
    let chars = Array.concat([[|'a' .. 'z'|];[|'A' .. 'Z'|];[|'0' .. '9'|]])
    let sz = Array.length chars in
    String(Array.init n (fun _ -> chars.[r.Next sz]))

let getHash inputStr M : int =
    let hashBytes = Encoding.UTF8.GetBytes(inputStr |> string) |> (new SHA256Managed()).ComputeHash
    //val hashBytes = MessageDigest.getInstance("SHA-1").digest(inputStr.getBytes("UTF-8"))
    let first4Bytes = hashBytes.[0..4]
    //printfn "byte 0: %i" hashBytes.[0]
    let mutable hashCode = 0
    for i in 0..4 do
        hashCode <- (hashCode <<< 8) + int (first4Bytes.[i] &&& byte 0xff)

    let mask = int (byte 0xffffffff >>> (32 - M))
    hashCode <- hashCode &&& mask
    hashCode

let getRandomHash M : int = 
    getHash (ranStr 32) M

let toList s = Set.fold (fun l se -> se::l) [] s

let NodeActor bossNode requests nodes selfID n (mailbox:Actor<_>) =
    let self = mailbox.Self
    let mutable fingerTable = Map.empty<int, IActorRef>
    let mutable fingerPeerID = Map.empty<int, int>
    let mutable requests = -1
    let mutable totalHops = 0
    let mutable messages = 0
    let mutable cancelRequesting = false
    let totalNodes = nodes

    let canReplace (peerID: int) = 
        let mutable distance = 0
        if(selfID < peerID) then
            distance <- peerID - selfID
        else
            distance <- selfID + int(2. ** 4.) - peerID

        let mutable closest = int(2. ** (Math.Log2(float distance)/Math.Log2(2.)))
        closest <- (closest + selfID) % n
        match fingerPeerID.TryFind(closest) with
            | Some x ->
                if x = -1 then
                    true
                else
                    (fingerPeerID.[closest] >= peerID)
            | None -> true

    let rec loop () = actor {
        let! message = mailbox.Receive()
        let sender = mailbox.Sender()

        match message with
        | SetFingerTable(x, y) ->   fingerTable <- x
                                    fingerPeerID <- y
        | Join(peerID,peer) ->  printfn "Peer %i has joined the ring" peerID
                                fingerTable |> Map.iter (fun _key _value ->
                                    if canReplace peerID then
                                        fingerTable <- fingerTable |> Map.add _key peer
                                        fingerPeerID <- fingerPeerID |> Map.add _key peerID
                                )
                                fingerTable <- fingerTable |> Map.add peerID peer
                                peer <! UpdateFingerTable(fingerTable, fingerPeerID)
        | UpdateFingerTable(x, y) ->    //Function that takes an incoming PeerTable and matches it with the current peer table and updates values
                                        printfn "Peer %i is updating its fingerTable" selfID
                                        let mutable updateSuccessorRequest = false
                                        fingerPeerID |> Map.iter (fun key' value' ->
                                            let mutable lowestValue =
                                                if value' = -1 then
                                                    int (2. ** float n)
                                                else
                                                    value'
                                            let mutable leastKey = int (2. ** float n)        
                                            y |> Map.iter (fun _key _value ->
                                                if _value < lowestValue && _value >= key' then
                                                    lowestValue <- _value
                                                    leastKey <- _key
                                            )
                                            if leastKey <> (int (2. ** float n)) then
                                                fingerPeerID <- fingerPeerID |> Map.add key' lowestValue
                                                fingerTable <- fingerTable |> Map.add key' x.[leastKey]
                                                updateSuccessorRequest <- true
                                        )
                                        if updateSuccessorRequest then
                                            self <! UpdateSuccessors
        | UpdateSuccessors ->   fingerTable |> Map.iter (fun key_ value_ ->
                                if not (isNull value_) then
                                    value_ <! RequestFingerTables(self)
                                )
        | RequestFingerTables x -> x <! UpdateFingerTable(fingerTable, fingerPeerID)
        | StartRequesting -> //Starts Scheduler to schedule SendRequest Message to self mailbox
                             system.Scheduler.ScheduleTellRepeatedly(TimeSpan.FromSeconds(1.), TimeSpan.FromSeconds(1.), self, SendRequest)
                             self <! SendRequest
        | SendRequest ->    //Send a request for a random peer over here
                            let randomPeer = r.Next(totalNodes)
                            
                            printfn "random peer: %i" randomPeer
                            match fingerTable.TryFind(randomPeer) with
                                | Some x -> printfn "some"
                                            x <! Request(self, 1)
                                | None -> printfn "none"
                                            //let mutable closest = -1
                                            //fingerTable |> Map.iter (fun _key _value -> if (_key < randomPeer || _key > closest) then closest <- _key)
                                            //fingerTable.[closest] <! RequestFwd(randomPeer, self, 1)*)
        | Request(actor,hops) ->    printfn "requesting!!!"
                                    totalHops <- totalHops + hops
                                   //actor <! Receipt
        | Receipt ->    messages <- messages + 1
                        if messages = requests then
                            cancelRequesting <- true
                            bossNode <! NodeAddComplete(totalHops)
                        printfn "message received at designated peer"
        | RequestFwd(reqID, requestingPeer, hops) -> match fingerTable.TryFind(reqID) with
                                                        | Some actor -> actor <! Request(requestingPeer, hops + 1)
                                                        | None ->   let mutable closest = -1
                                                                    fingerTable |> Map.iter (fun _key _value -> if (_key < reqID || _key > closest) then closest <- _key)
                                                                    fingerTable.[closest] <! RequestFwd(reqID, requestingPeer, hops + 1)
        | _ -> ()
        return! loop ()
    }
    loop ()

let BossActor nodes (mailbox:Actor<_>) =
    let mutable totalNodes = nodes
    let mutable totalHops = 0
    let mutable addedNodes = 0
    let mutable requests = 0

    let rec loop () = actor {
        let! message = mailbox.Receive()
        let sender = mailbox.Sender()

        match message with
        | NodeAddComplete hops ->   addedNodes <- addedNodes + 1
                                    totalHops <- totalHops + hops
                                    
                                    if (addedNodes = totalHops) then
                                        printfn "All the nodes have completed the number of requests to be made with %f average hops" (float(totalHops)/float(requests*totalNodes))
                                        Environment.Exit(-1)
        | SetRequests requests_ ->    requests <- requests_
        | _ -> ()
        return! loop ()
    }
    loop ()

let nearestPower n =
    if ((n > 0) && (n &&& (n-1) = 0)) then
        n
    else
        let mutable count = 0
        let mutable x = n
        while (x <> 0) do
            x <- x >>> 1
            count <- count + 1
        count

match fsi.CommandLineArgs.Length with
| 3 ->
    let mutable numNodes = 5//let numNodes = fsi.CommandLineArgs.[1] |> int
    let numRequests = 10//let numRequests = fsi.CommandLineArgs.[2] |> int

    //timer.Start()

    let bossNode = spawn system "boss" (BossActor numNodes)

    printfn "num nodes: %i" numNodes
    let nearestPow = nearestPower numNodes
    let ringCapacity = int (2.**float nearestPow)

    printfn "Nearest Power: %i, Ring Capacity: %i" nearestPow ringCapacity
    
    bossNode <! SetRequests(numRequests)

    let nodes = [|for i in [0..numNodes-1] -> NodeActor bossNode numRequests numNodes i nearestPow |> spawn system ("Node" + string(i))|]

    for i in [0 .. numNodes-1] do
        let mutable fingers = Map.empty<int, IActorRef>
        let mutable peerIDTable = Map.empty<int, int>
        fingers <- fingers |> Map.add i nodes.[i]
        for j in [0 .. nearestPow - 1] do
            let x = i + int (2. ** float j) % int (2.** float nearestPow)
            fingers <- fingers |> Map.add x null
            peerIDTable <- peerIDTable |> Map.add x -1
        nodes.[i] <! SetFingerTable(fingers, peerIDTable)

    let baseActor = nodes.[0]
    for i in [1 .. numNodes-1] do
        baseActor <! Join(i, nodes.[i])
    
    //for i in [0 .. numNodes-1] do
    nodes.[0] <! StartRequesting

    system.WhenTerminated.Wait()
    ()
| _ -> failwith "Error, wrong number of arguments, run program with command: 'dotnet fsi Project3.fsx <numNodes> <numRequests>'"
