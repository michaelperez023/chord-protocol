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
let m = int (ceil (Math.Log(float Int32.MaxValue, 10.0) / Math.Log(2.0, 10.0))) - 1
let totalSpace = int64 (2.0**(float m))

type Message =
    | Start
    | Join of IActorRef
    | NodeAddComplete

let ranStr n = 
    let r = Random()
    let chars = Array.concat([[|'a' .. 'z'|];[|'A' .. 'Z'|];[|'0' .. '9'|]])
    let sz = Array.length chars in
    String(Array.init n (fun _ -> chars.[r.Next sz]))

//let bytesToHex : byte[] -> String =
//    fun bytes -> bytes |> Array.fold (fun a x -> a + x.ToString("x2")) ""

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

(*let getHash id totalSpace =
    printfn "id: %s" id
    let mutable hash = (0 |> int64)
    if not (String.IsNullOrEmpsty(id)) then
        let mutable key = Encoding.UTF8.GetBytes(id) |> (new SHA256Managed()).ComputeHash |> bytesToHex
        //var key = MessageDigest.getInstance("SHA-256").digest(id.getBytes("UTF-8")).map("%02X" format _).mkString.trim()
        if key.Length > 15 then
            key <- key.Substring(key.Length - 15)
        printfn "key: %s" key
        hash <- (key |> int64) % totalSpace
    hash*)

type Interval(s:int, e:int, m:int) =
    static let determineZeroCrossOver (st:int) (en:int) =
        if st > en then true else false
    member this.StartInterval = s
    member this.EndInterval = e
    member this.M = m
    member this.ringLimit = int(2.0**(double m))
    member this.zeroCrossOver = determineZeroCrossOver s e

    member this.contains (i:int) : bool =
        let mutable inRange = false
        if ((i >= this.StartInterval) && (i < this.EndInterval)) then
            inRange <- true
        else if this.zeroCrossOver && ((i >= this.StartInterval && i < this.ringLimit) || (i >= 0 && i < this.EndInterval)) then
            inRange <- true
        inRange

type FingerTableEntry(s:int, interval:Interval, actorRef:IActorRef) =
    member this.toString : String =
        actorRef.ToString()

let NodeActor index M (mailbox:Actor<_>) =
    let sizeLimit = int (2.0**(double M))
    let mutable fingerTable : FingerTableEntry array = Array.zeroCreate M

    for i in 0..M-1 do
        let start = int (index + int(2.0**(double i))) % sizeLimit
        let interval = new Interval(start, ((start + int (2.0**(double i))) % sizeLimit), M)
        fingerTable.[i] <- new FingerTableEntry(start, interval, mailbox.Self)

    let mutable nodeIDs = Set.empty
    let rec loop () = actor {
        let! message = mailbox.Receive()
        let sender = mailbox.Sender()

        match message with
        | Join(networkNode) ->  if networkNode = null then
                                    printfn "network node is null"
                                else
                                    printfn "network node is not null"
                                sender <! NodeAddComplete
        | _ -> ()
        return! loop ()
    }
    loop ()

let BossActor numNodes numRequests (mailbox:Actor<_>) =
    let mutable nodeIDs = Set.empty
    let mutable addedNodes = 0
    let mutable nodeIDsList = List.empty
    let rec loop () = actor {
        let! message = mailbox.Receive()
        let sender = mailbox.Sender()

        match message with
        | Start ->  printfn "random hash 1 %i" (getRandomHash(30))
                    nodeIDs <- nodeIDs.Add(getRandomHash(30))
                    let mutable randInt = 0
                    randInt <- getRandomHash(30)
                    while (nodeIDs.Count < numNodes) do
                        if nodeIDs.Contains(randInt) then
                            randInt <- getRandomHash(30)
                        else
                            nodeIDs <- nodeIDs.Add(randInt)
                    nodeIDsList <- toList nodeIDs
                    let node1Name = nodeIDsList.[0]
                    printfn "spawning node %i" node1Name

                    let node1 = NodeActor node1Name 30 |> spawn system ("Node" + string(node1Name))
                    node1 <! Join(null)
                    printfn "node 1 joining"
        | NodeAddComplete ->    addedNodes <- addedNodes + 1
                                printfn "node add complete"

                                if addedNodes <> numNodes then
                                    let nodeId = nodeIDsList.[addedNodes]
                                    let node = NodeActor nodeId 30 |> spawn system ("Node" + string(nodeId))
                                    node <! Join(null)
                                else
                                    printfn "All nodes added"
        | _ -> ()
        return! loop ()
    }
    loop ()

match fsi.CommandLineArgs.Length with
| 3 ->
    let numNodes = fsi.CommandLineArgs.[1] |> int
    let numRequests = fsi.CommandLineArgs.[2] |> int

    //timer.Start()

    let bossNode = spawn system "boss" (BossActor numNodes numRequests)
    
    bossNode <! Start

    //for i in [0..numNodes-1] do
    //    if i = 0 then
     //       let node1 = getHash ("Node - " + (i |> string)) totalSpace
     //       printfn "Initializing the first peer with hash Id %i" node1

    system.WhenTerminated.Wait()
    ()
| _ -> failwith "Error, wrong number of arguments, run program with command: 'dotnet fsi Project3.fsx <numNodes> <numRequests>'"
