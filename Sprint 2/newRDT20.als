open util/ordering[State]

//represents the Sender of data
lone sig Sender{}
//represents the Channel that data travels through when sent
lone sig Channel{}
//represents the Receiver of the data
lone sig Receiver{}

sig Checksum{}

one sig checkRelData{
	rel: Data one -> one Checksum
}{ all d: Data| all c: Checksum|  #(rel).c = 1 and 
		 #d.(rel) = 1
}
//represents the data that we are trying to send
sig Data{}

//represents the containers of data during transfer
sig Packet{
	ch: one Checksum,
	payload: one Data
}

//represents an instance in time
sig State{
	//The data that still needs to be sent
	toSend: Sender lone -> set Data,
	//The packets that are curently being sent
	inTransit: Channel lone -> lone Packet,
	//The data that has been received
	received: Receiver lone -> set Data,
}

fun calcChecksum[d: Data]  : one Checksum{
	d.(checkRelData.rel)
}
//Sets the initial status of the model
pred init[s: State]{
	//All data is in the list of data to be sent
	all d: Data | d in Sender.(s.toSend)
	//5 instances of data exist
	#s.toSend = 5
	#Checksum = #Data
	#Packet = #Data
	//Nothing is being sent
	#s.inTransit = 0
	//Nothing has been received
	#s.received = 0
}

//Perform a send followed by a receive
pred twoStepA[s, s', s'': State]{
	send[s, s']
	receive[s', s'']
}

//Perform a send followed by a receive
pred twoStepB[s, s', s'': State]{
	receive[s, s']
	send[s', s'']
}

//Send an instance of data by removing it from the list of data
//to send and placing it in a Packet which is placed inTransit
pred send[s, s': State]{
	one d: Sender.(s.toSend) | one p: Packet | Sender.(s'.toSend) = Sender.(s.toSend) - d and
		Channel.(s'.inTransit) = p and #Channel.(s.inTransit) = 0 and 
		(Channel.(s'.inTransit)).payload = d and s.received = s'.received
}

//Receive an instance of data by removing it from the list of
//Packets in transit and placing it in the list of received data
pred receive[s, s': State]{
	one p: Channel.(s.inTransit) |
		Receiver.(s'.received) = Receiver.(s.received) + p.payload and #Channel.(s'.inTransit) = 0 and s.toSend = s'.toSend
}

//Just show some states
pred show{
	some State
}

//Trace a successful run of the model
pred traceTwoStep{
	init[first]
	all s: ( State-last - last.prev) | let s' = s.next | let s'' = s'.next |
		twoStepA[s, s', s''] or twoStepB[s,s',s'']
}

run show

//11 states
run traceTwoStep for 11
