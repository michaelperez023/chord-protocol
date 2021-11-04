// Authors: Blas Kojusner and Michael Perez - UFID: 62498470 - Distributed Operating Systems - COP5615 - Project3
#time "on"
#r "nuget: Akka.FSharp"

open System
open Akka.Actor
open Akka.FSharp
open System.Security.Cryptography
open System.Collections.Generic

let system = ActorSystem.Create("System")
let r = Random()
let nodeDict = new Dictionary<bigint, IActorRef>()

type Message =
    | BossStart
    | NodeStart
    | Complete of int * bigint
    | Initialize of bigint * int * List<bigint> * bigint * bigint * int * List<bigint>
    | Update of bigint * int * int
    | Join of bigint
    | FindPredecessor of int * int
    | CheckPredecessor
    | RequestMessage of string * bigint * bigint * int
    | RequestReachedDestination of int
    | FindSuccessorMessage of bigint
    | SuccessorFoundMessage of bigint * bigint * List<bigint>
    | PredecessorReply
    | SuccessorCheckingPredecessor

let ranStr n = 
    let r = Random()
    let chars = Array.concat([[|'a' .. 'z'|];[|'A' .. 'Z'|];[|'0' .. '9'|]])
    let sz = Array.length chars in
    String(Array.init n (fun _ -> chars.[r.Next sz]))

let stringToByte(str: string) = System.Text.Encoding.ASCII.GetBytes(str);

let routeNode(hash':bigint, id':bigint, predecessor':bigint, successor':bigint, fingerTable':List<bigint>, successorList':List<bigint>) = 
    let mutable destination = id'
    let mutable fingers = List<bigint>()
    for i in fingerTable' do
        fingers.Add(i) |> ignore
    for i in successorList' do
        fingers.Add(i) |> ignore
    fingers.Sort()
    
    if ((((hash' <= id') || (hash' > id' && (hash' > predecessor'))) && (predecessor' > id') || (((hash' > predecessor') && (hash' <= id')))) && (predecessor' < id')) && (predecessor' <> bigint(-1)) then
        destination <- id'
    else if hash' < fingers.Item(0) || hash' > fingers.Item(fingers.Count - 1) then
        destination <- fingers.Item(fingers.Count - 1)
    else if (id' < successor' && (hash' > id' && hash' <= successor')) || (id' > successor' && ((hash' < id' && hash' <= successor') || hash' > id')) then
        destination <- successor'
    else
        for i in 0..fingers.Count - 1 do
            if hash' > fingers.Item(i) && hash' <= fingers.Item(i+1) then
                destination <- fingers.Item(i)
    destination

let NodeActor (mailbox:Actor<_>) =
    let mutable numRequests = 0
    let mutable messagesReceived = 0
    let mutable id = bigint(-1)
    let mutable fingerTable = new List<bigint>()
    let mutable predecessor = bigint(-1)
    let mutable successor = bigint(-1)
    let mutable successorList = new List<bigint>()
    let mutable m = -1
    let mutable numHops = 0
    let mutable predecessorExists:bool = true
    let mutable boss = mailbox.Self

    let rec loop () = actor {
        mailbox.Context.SetReceiveTimeout(TimeSpan.FromSeconds 1000.0)
        let! message = mailbox.Receive()
        if boss = mailbox.Self then
            boss <- mailbox.Sender()

        match message with
        | Initialize(id', m', fingerTable', predecessor', successor', numRequests', successorList') -> 
            id <- id'
            m <- m'
            fingerTable <- fingerTable'
            predecessor <- predecessor'
            successor <- successor'
            numRequests <- numRequests'
            successorList <- successorList'
        | Update(id', m', numRequests') -> 
            id <- id'
            m <- m'
            numRequests <- numRequests'
        | NodeStart -> 
            // Generate random text from some random string
            let mutable randomText = ranStr 5
            let hash = abs(bigint(stringToByte(randomText) |> HashAlgorithm.Create("SHA1").ComputeHash)) % bigint(Math.Pow(2.0, float(m)))
            let destination = routeNode(hash, id, predecessor, successor, fingerTable, successorList)
            nodeDict.Item(destination) <! RequestMessage(randomText, hash, id, 0)
            system.Scheduler.ScheduleTellOnce(TimeSpan.FromSeconds(1.), mailbox.Self, NodeStart) // send request once/second
        | RequestMessage(message', hash', id', hops') -> 
            let destination = routeNode(hash', id, predecessor, successor, fingerTable, successorList)
            let newHops = hops' + 1
            if destination = id then
                nodeDict.Item(id') <! RequestReachedDestination(newHops)
            else
                nodeDict.Item(destination) <! RequestMessage(message', hash', id', newHops)
        | RequestReachedDestination(hops') ->
            messagesReceived <- messagesReceived + 1
            numHops <- numHops + hops'
            if messagesReceived = numRequests then
                boss <! Complete(numHops, id)
        | Join(rNode) -> 
            nodeDict.Item(rNode) <! FindSuccessorMessage(id)
        | FindSuccessorMessage(node) -> 
            let destination = routeNode(node, id, predecessor, successor, fingerTable, successorList)
            if destination = id && predecessor <> bigint(-1) then
                nodeDict.Item(node) <! SuccessorFoundMessage(id, predecessor, successorList)
                predecessor <- node
            else
                nodeDict.Item(destination) <! FindSuccessorMessage(node)
        | SuccessorFoundMessage(successor', predecessor', successorList') ->
            successor <- successor'
            predecessor <- predecessor'
            fingerTable.Add(successor')
            successorList.Add(successor')
            for i in successorList' do
                successorList.Add(i)
            successorList.Sort()
            nodeDict.Item(id) <! NodeStart
        | CheckPredecessor ->
            if predecessor <> bigint(-1) then
                if predecessorExists then
                    nodeDict.Item(predecessor) <! SuccessorCheckingPredecessor
                    predecessorExists <- false
                else
                    predecessor <- bigint(-1)
            system.Scheduler.ScheduleTellOnce(TimeSpan.FromMilliseconds(500.0), mailbox.Self, CheckPredecessor)
        | SuccessorCheckingPredecessor -> 
            nodeDict.Item(successor) <! PredecessorReply
        | PredecessorReply -> 
            predecessorExists <- true
        | _ -> ()
        return! loop ()
    }
    loop ()

let BossActor numNodesInput numRequests (mailbox:Actor<_>) =
    // Setting values for the variables that we will be using
    let mutable nodeIdDict = new Dictionary<int, bigint>()
    let mutable completedNodes = 0
    let mutable numNodes = 0
    let mutable numNodesLeft = 0
    let mutable totalHops = 0L
    let mutable requests = numRequests;

    // Preprocessing of node counts which divides the inputs into a value of the majority of nodes while taking out 10 nodes.
    // Could be modified easily to have a default value set to less than 100 and then check for greater than 100
    if numNodesInput <= 100 then
        numNodes <- (numNodesInput - int(0.1 * float(numNodesInput)))
        numNodesLeft <- (int(0.1 * float(numNodesInput)))
    else
        numNodes <- numNodesInput - 10
        numNodesLeft <- 10
    //numNodes <- numNodesInput
    //numNodesLeft <- 5
    printfn "nodes: %i" numNodes
    printfn "numNodesLeft: %i" numNodesLeft

    // Start the process of deciding what to do with the message recieved
    let rec loop () = actor {
        let! message = mailbox.Receive()
        match message with
        | BossStart -> // Start boss
            // Assign the identifier length of m, used to identify nodes
            let m = int(ceil((Math.Log(float(numNodes), 2.0))) * 3.0)
            printfn "m: %i" m

            // Iterate through each node in the total number of nodes we have
            // Assign them a name, create their hash based on their name and set an ID for their search
            // Add these values to the nodeDictionary and the IdDictionary
            for i in 1..numNodes do
                let name = "peer" + (i.ToString())
                let hash = stringToByte(name) |> HashAlgorithm.Create("SHA1").ComputeHash
                let id = abs(bigint(hash)) % bigint(Math.Pow(2.0, double(m)))
                nodeDict.Add(id, spawn system ("Node" + string(id)) NodeActor)
                nodeIdDict.Add(i, id)

            // Now create a list of all the nodeIDs that were generated and then sort it
            let mutable nodeIdList = new List<bigint>()
            for i in nodeIdDict.Values do
                nodeIdList.Add(i)
            nodeIdList.Sort()

            // Not sure why the indexing begins at 0 now instead of 1
            // Iterate through each item again from the total number of nodes we have
            // Gather all the information we will need to start a new node (Lists, Tables, Indexs, etc.)
            for i in 0..numNodes-1 do
                // Now we assign values that will be used for the fingerTable and the successorList
                let mutable fingerTableSet = new HashSet<bigint>()
                let mutable fingerTable = new List<bigint>()
                let mutable successorList = new List<bigint>()

                for j in 0..m-1 do 
                    // Get neighbor in chord
                    let neighbor = nodeIdDict.Item(i+1) + bigint(int(Math.Pow(2.0, float(j)))) % bigint(Math.Pow(2.0, float(m)))
                    let mutable biggerFound:bool = false;
                    
                    // Add a bigger node, if found, to the chord
                    for k in 0..nodeIdList.Count-1 do
                        if neighbor <= nodeIdList.Item(k) && not biggerFound then
                            fingerTableSet.Add(nodeIdList.Item(k)) |> ignore
                            biggerFound <- true
                    
                    // This seems to re-arrange the neighbors to be properly ordered
                    if neighbor > nodeIdList.Item(nodeIdList.Count - 1) then
                        fingerTableSet.Add(nodeIdList.Item(0)) |> ignore
                
                // FingerTableSet seems to be a sorted fingertable with the hash values
                for l in fingerTableSet do
                    fingerTable.Add(l)
                fingerTable.Sort()

                // Gets sorted index list of all the nodes based off their IDs
                let nodeIndexSortedList = nodeIdList.IndexOf(nodeIdDict.Item(i+1))
                
                // Create a list of all the successors based off the newly sorted node index and ID list
                for m in 1..int((ceil(Math.Log(float(numNodes), 2.0)))) do
                    let successorIndex = (nodeIndexSortedList + m) % nodeIdList.Count
                    successorList.Add(nodeIdList.Item(successorIndex))
                
                // Set the predecessor based on the node ID list and the location of the items in the node
                let mutable predecessor = bigint(-1);
                if nodeIdList.IndexOf(nodeIdDict.Item(i + 1)) > 0 then
                    predecessor <- nodeIdList.Item(nodeIdList.IndexOf(nodeIdDict.Item(i+1)) - 1)
                else
                    predecessor <- nodeIdList.Item(nodeIdList.Count - 1)

                // Set what the successor will be at the current moment for the node based on the ID list
                // Could be combined with the logic of collecting the successor list
                let mutable successor = bigint(-1);
                if nodeIdList.IndexOf(nodeIdDict.Item(i + 1)) + 1 < nodeIdList.Count then
                    successor <- nodeIdList.Item(nodeIdList.IndexOf(nodeIdDict.Item(i+1)) + 1)
                else
                    successor <- nodeIdList.Item(0)
                // Done setting all the values, lists, and indexes that each node will hold
                // Initialize a node with the data that we currently have available
                nodeDict.Item(nodeIdDict.Item(i + 1)) <! Initialize((nodeIdDict.Item(i+1)), m, fingerTable, predecessor, successor, requests, successorList)
            
            // Each node has been initialized, so start each one
            for i in 1..numNodes do
                nodeDict.Item(nodeIdDict.Item(i)) <! NodeStart

            // Iterate through nodes left
            for i in (numNodes+1)..(numNodes+numNodesLeft) do
                // Assign their name, hash and ID similarly as we have done before
                let name = "peer" + (i.ToString())
                let hash = stringToByte(name) |> HashAlgorithm.Create("SHA1").ComputeHash
                let id = abs(bigint(hash)) % bigint(Math.Pow(2.0, double(m)))

                // Add them to the nodeDict and the nodeIdDict
                nodeDict.Add(id, spawn system ("Node" + string(id)) NodeActor)
                nodeIdDict.Add(i, id)

                // Once they are added to the Dict and IdDict we want to update that value
                nodeDict.Item(nodeIdDict.Item(i)) <! Update((nodeIdDict.Item(i), m, requests))
            
            let mutable nodeIdListNew = new List<bigint>()
            for i in nodeIdDict.Values do
                nodeIdListNew.Add(i)
            nodeIdListNew.Sort()
            for i in (numNodes+1)..(numNodes+numNodesLeft) do
                let mutable rNode = nodeIdListNew.Item(r.Next(nodeIdList.Count - 1))
                nodeDict.Item(nodeIdDict.Item(i)) <! Join(rNode)
        | Complete(hops, node) -> // Node completion check
            // Increment completed nodes
            completedNodes <- completedNodes + 1

            // Print node that just finished if number of completed nodes is less than total 
            if completedNodes <= (numNodes + numNodesLeft) then
                printfn "Node %A completed after %d hops. %d nodes have completed." node hops completedNodes
                totalHops <- totalHops + int64(hops)

            // Exit program if number of completed nodes is equal to number of nodes
            if completedNodes = numNodes then
                let avgHops = float(totalHops) / (float(numNodes + numNodesLeft) * float(numRequests))
                printfn "Total hops: %i %f" numNodes avgHops
                exit 0
        | _ -> ()
        return! loop ()
    }
    loop ()

match fsi.CommandLineArgs.Length with
| 3 ->
    // First input is number of nodes, second input is number of requests per node
    let numNodes = fsi.CommandLineArgs.[1] |> int
    let numRequests = fsi.CommandLineArgs.[2] |> int

    // Go ahead and spawn the boss node with the number of nodes and requests we set
    let bossNode = spawn system "boss" (BossActor numNodes numRequests)
    
    // Start the boss node with the actor message BossStart
    bossNode <! BossStart

    system.WhenTerminated.Wait()
    ()
| _ -> failwith "Error, wrong number of arguments, run program with command: 'dotnet fsi Project3.fsx <numNodes> <numRequests>'"
