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

// Switch up the order of inputs
type Message =
    | BossStart
    | CheckPredecessor
    | Complete of int * bigint
    | GetSuccessor of bigint
    | Initialize of bigint * bigint * bigint * int * int * List<bigint> * List<bigint>
    | Join of bigint
    | NodeStart
    | PredecessorCheck
    | Request of string * int * bigint * bigint
    | RequestRouted of int
    | SuccessorCheck of bigint * bigint * List<bigint>
    | SuccessorPredecessorCheck
    | Update of int * int * bigint
    
let ranStr n = 
    let chars = Array.concat([[|'a' .. 'z'|];[|'A' .. 'Z'|];[|'0' .. '9'|]])
    let sz = Array.length chars in String(Array.init n (fun _ -> chars.[r.Next sz]))

let NodeActor (mailbox:Actor<_>) =
    let mutable numRequests = 0
    let mutable messagesReceived = 0
    let mutable id = bigint(-1)
    let mutable fingerTable = new List<bigint>()
    let mutable predecessor = bigint(-1)
    let mutable successor = bigint(-1)
    let mutable successors = new List<bigint>()
    let mutable m = -1
    let mutable predecessorCheck:bool = true
    let mutable numHops = 0
    let mutable boss = mailbox.Self

    let routeNode(hash':bigint, id':bigint, predecessor':bigint, successor':bigint, fingerTable':List<bigint>, successors':List<bigint>) = 
        let mutable fingers = List<bigint>()
        for i in fingerTable' do
            fingers.Add(i) |> ignore
        for i in successors' do
            fingers.Add(i) |> ignore
        fingers.Sort()
        
        let mutable slot = id'
        if ((((hash' <= id') || (hash' > id' && (hash' > predecessor'))) && (predecessor' > id') || (((hash' > predecessor') && (hash' <= id')))) && (predecessor' < id')) && (predecessor' <> bigint(-1)) then
            slot <- id'
        else if hash' < fingers.Item(0) || hash' > fingers.Item(fingers.Count - 1) then
            slot <- fingers.Item(fingers.Count - 1)
        else if (id' < successor' && (hash' > id' && hash' <= successor')) || (id' > successor' && ((hash' < id' && hash' <= successor') || hash' > id')) then
            slot <- successor'
        else
            for i in 0..fingers.Count - 1 do
                if hash' > fingers.Item(i) && hash' <= fingers.Item(i+1) then
                    slot <- fingers.Item(i)
        slot

    let rec loop () = actor {
        let! message = mailbox.Receive()
        if boss = mailbox.Self then
            boss <- mailbox.Sender()

        match message with
        | Join(node) -> 
            nodeDict.Item(node) <! GetSuccessor(id)
        | Initialize(id', predecessor', successor', m', numRequests', successors', fingerTable') -> 
            id <- id'
            predecessor <- predecessor'
            successor <- successor'
            m <- m'
            numRequests <- numRequests'
            successors <- successors'
            fingerTable <- fingerTable'
        | Update(m', numRequests', id') -> 
            m <- m'
            numRequests <- numRequests'
            id <- id'
        | NodeStart -> 
            // Generate random text from some random string
            let mutable randomText = ranStr 5
            let hash = abs(bigint(System.Text.Encoding.ASCII.GetBytes(randomText) |> HashAlgorithm.Create("SHA1").ComputeHash)) % bigint(Math.Pow(2.0, float(m)))
            let slot = routeNode(hash, id, predecessor, successor, fingerTable, successors)
            nodeDict.Item(slot) <! Request(randomText, 0, hash, id)
            system.Scheduler.ScheduleTellOnce(TimeSpan.FromSeconds(1.), mailbox.Self, NodeStart) // send request once/second
        | Request(message', hops', hash', id') -> 
            let slot = routeNode(hash', id, predecessor, successor, fingerTable, successors)
            let hopsCounter = hops' + 1
            if slot = id then
                nodeDict.Item(id') <! RequestRouted(hopsCounter)
            else
                nodeDict.Item(slot) <! Request(message', hopsCounter, hash', id')
        | RequestRouted(hops') ->
            numHops <- numHops + hops'
            messagesReceived <- messagesReceived + 1
            if messagesReceived = numRequests then
                boss <! Complete(numHops, id)
        | GetSuccessor(node) -> 
            let slot = routeNode(node, id, predecessor, successor, fingerTable, successors)
            if slot = id && predecessor <> bigint(-1) then
                nodeDict.Item(node) <! SuccessorCheck(id, predecessor, successors)
                predecessor <- node
            else
                nodeDict.Item(slot) <! GetSuccessor(node)
        | SuccessorCheck(successor', predecessor', successors') ->
            fingerTable.Add(successor')
            successors.Add(successor')
            predecessor <- predecessor'
            successor <- successor'
            for i in successors' do
                successors.Add(i)
            successors.Sort()
            nodeDict.Item(id) <! NodeStart
        | CheckPredecessor ->
            if predecessor <> bigint(-1) then
                if not predecessorCheck then
                    predecessor <- bigint(-1)
                else
                    nodeDict.Item(predecessor) <! SuccessorPredecessorCheck
                    predecessorCheck <- false
            system.Scheduler.ScheduleTellOnce(TimeSpan.FromSeconds(0.5), mailbox.Self, CheckPredecessor)
        | SuccessorPredecessorCheck -> 
            nodeDict.Item(successor) <! PredecessorCheck
        | PredecessorCheck -> 
            predecessorCheck <- true
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
    let mutable requests = numRequests;
    let mutable totalHops = 0  

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
    printfn "Number of nodes: %i" numNodes
    printfn "Number of nodes left: %i" numNodesLeft

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
                let hash = System.Text.Encoding.ASCII.GetBytes(name) |> HashAlgorithm.Create("SHA1").ComputeHash
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
                // Now we assign values that will be used for the fingerTable and the successors
                let mutable fingerTableSet = new List<bigint>()
                let mutable fingerTable = new List<bigint>()
                let mutable successors = new List<bigint>()
                for j in 0..m-1 do 
                    // Get neighbor in chord
                    let neighbor = nodeIdDict.Item(i+1) + bigint(int(Math.Pow(2.0, float(j)))) % bigint(Math.Pow(2.0, float(m)))
                    let mutable biggerFound:bool = false;
                    
                    // Add a bigger node, if found, to the chord
                    for k in 0..nodeIdList.Count-1 do
                        if neighbor <= nodeIdList.Item(k) && not biggerFound then
                            fingerTableSet.Add(nodeIdList.Item(k)) |> ignore
                            biggerFound <- true
                    
                    // This re-arranges the neighbors
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
                    successors.Add(nodeIdList.Item(successorIndex))
                
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
                nodeDict.Item(nodeIdDict.Item(i + 1)) <! Initialize((nodeIdDict.Item(i+1)), predecessor, successor, m, requests, successors, fingerTable)
            
            // Each node has been initialized, so start each one
            for i in 1..numNodes do
                nodeDict.Item(nodeIdDict.Item(i)) <! NodeStart

            // Iterate through nodes left
            for i in (numNodes+1)..(numNodes+numNodesLeft) do
                // Assign their name, hash and ID similarly as we have done before
                let name = "peer" + (i.ToString())
                let hash = System.Text.Encoding.ASCII.GetBytes(name) |> HashAlgorithm.Create("SHA1").ComputeHash
                let id = abs(bigint(hash)) % bigint(Math.Pow(2.0, double(m)))

                // Add them to the nodeDict and the nodeIdDict
                nodeDict.Add(id, spawn system ("Node" + string(id)) NodeActor)
                nodeIdDict.Add(i, id)

                // Once they are added to the Dict and IdDict we want to update that value
                nodeDict.Item(nodeIdDict.Item(i)) <! Update((m, requests, nodeIdDict.Item(i)))
            
            let mutable nodeIdListNew = new List<bigint>()
            for i in nodeIdDict.Values do
                nodeIdListNew.Add(i)
            nodeIdListNew.Sort()
            for i in (numNodes+1)..(numNodes+numNodesLeft) do
                let mutable rNode = nodeIdListNew.Item(r.Next(nodeIdList.Count - 1))
                nodeDict.Item(nodeIdDict.Item(i)) <! Join(rNode)
        | Complete(hops, node) -> // Node completion check
            // Print node that just finished if number of completed nodes is less than total 
            printfn "Node %A completed after %d hops. %d nodes have completed." node hops completedNodes
            totalHops <- totalHops + hops
            completedNodes <- completedNodes + 1 // Increment completed nodes

            // Exit program if number of completed nodes is equal to number of nodes
            if completedNodes = numNodes then
                printfn "Total nodes: %i" numNodes
                printfn "Total hops: %i" totalHops
                printfn "Average hops: %f" (float(totalHops) / (float(numNodes + numNodesLeft) * float(numRequests)))
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

    // Spawn the boss node with the inputted number of nodes and requests
    let bossNode = spawn system "boss" (BossActor numNodes numRequests)
    
    // Start the boss node with the actor message BossStart
    bossNode <! BossStart

    system.WhenTerminated.Wait()
    ()
| _ -> failwith "Error, wrong number of arguments, run program with command: 'dotnet fsi Project3.fsx <numNodes> <numRequests>'"
