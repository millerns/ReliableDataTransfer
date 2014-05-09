open util/ordering[State]

//represents the Sender of data
lone sig Sender{}
//represents the Channel that data travels through when sent
lone sig Channel{}
//represents the Receiver of the data
lone sig Receiver{}

//represents the data that we are trying to send
sig Data{}

//represents the containers of data during transfer
sig Packet{}

//represents an instance in time
sig State{
	//The data that still needs to be sent
	toSend: Sender lone -> set Data,
	//The packets that are curently being sent
	inTransit: Channel lone -> set Packet,
	//The data that has been received
	received: Receiver lone -> set Data,
	//The data that is currently contained in a packet
	wrapped: set Packet -> lone Data
}

//Sets the initial status of the model
pred init[s: State]{
	//All data is in the list of data to be sent
	all d: Data | d in Sender.(s.toSend)
	//5 instances of data exist
	#s.toSend = 5
	//Nothing is being sent
	#s.inTransit = 0
	//Nothing has been received
	#s.received = 0
	//Nothing is in a Packet
	#s.wrapped = 0
}

//Perform a send followed by a receive
pred twoStepA[s, s', s'': State]{
	send[s, s']
	receive[s', s'']
}

//Perform a receive followed by a send
pred twoStepB[s, s', s'': State]{
	receive[s, s']
	send[s', s'']
}

//Send an instance of data by removing it from the list of data
//to send and placing it in a Packet which is placed inTransit
pred send[s, s': State]{
	some d: Data | some p: Packet | (d in Packet.(s'.wrapped)) and 
		(d in Sender.(s.toSend)) and (p in Channel.(s'.inTransit)) and
		(Sender.(s'.toSend) =( Sender.(s.toSend) - d)) and 
		(Channel.(s'.inTransit) = (Channel.(s.inTransit) + p)) and
		(Receiver.(s'.received) = Receiver.(s.received)) and
		(Packet.(s'.wrapped) = Packet.(s.wrapped) + d)
}

//Receive an instance of data by removing it from the list of
//Packets in transit and placing it in the list of received data
pred receive[s, s': State]{
	some d: Data | some p: Packet | (d in Packet.(s.wrapped)) and 
		(p in Channel.(s.inTransit)) and (d in Receiver.(s'.received)) and
		(Channel.(s'.inTransit) =( Channel.(s.inTransit) - p)) and 
		(Receiver.(s'.received) = (Receiver.(s.received) + d)) and
		(Sender.(s'.toSend) = Sender.(s.toSend))and
		(Packet.(s'.wrapped) = Packet.(s.wrapped) - d)
}

//Just show some states
pred show{
	some State
}

//Trace a successful run of the model
pred traceTwoStep{
	init[first]
	all s: State - (last + last.prev) | let s' = s.next | let s'' = s'.next |  
		twoStepA[s, s', s''] or twoStepB[s, s', s'']
}

//Trace a failing run of the model
pred traceTwoStepFail{
	init[first]
	all s: State - (last + last.prev) | let s' = s.next | let s'' = s'.next |  
		twoStepA[s, s', s''] or twoStepB[s, s', s'']
	not (Sender.(first.toSend) = Receiver.(last.received))
}


run show

//11 states
run traceTwoStep for 11

//11 states
run traceTwoStepFail for 11
