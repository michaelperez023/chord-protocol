# DOS-Project3 - Chord Protocol
Team Members: Blas Kojusner and Michael Perez

COP5615 - Dr. Alin Dobra

November 3 2021

How to run:
dotnet fsi Project2.fsx numNodes numRequests

numNodes is the number of peers, and numRequests is the number of requests each peer has to make. 

What is working:
The network join and routing as described in the Chord paper are both working. Keys are associated with a string, and when all peers have performs the number of requests specified in numRequests, the program exits. Each peer sends a request each second. The average number of hops that have to be traversed to deliver a message is printed. 

Rarely, when testing with small number, this error occurs, but this does not prevent the program from terminating:
"[ERROR][11/4/2021 3:34:55 AM][Thread 0016][akka://System/user/Node783406] Index was out of range. Must be non-negative and less than the size of the collection. (Parameter 'index')
Cause: System.ArgumentOutOfRangeException: Index was out of range. Must be non-negative and less than the size of the collection. (Parameter 'index')
   at FSI_0002.routeNode@48(BigInteger tupledArg0, BigInteger tupledArg1, BigInteger tupledArg2, BigInteger tupledArg3, List`1 tupledArg4, List`1 tupledArg5)"
   
The largest network we managed to deal with is 20,000 nodes, with 5 requests each. The average number of hops that had to be traversed in this network was 49.25.
