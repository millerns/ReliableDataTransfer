open util/ordering[State]
	
lone sig Sender{}
lone sig Channel{}
lone sig Receiver{}

sig Packet{}

sig State{
	toSend: Sender lone -> set Packet,
	inTransit: Channel lone -> set Packet,
	received: Receiver lone -> set Packet
}

pred init[s: State]{
	all p: Packet | p in Sender.(s.toSend)
	#s.toSend = 5
	#s.inTransit = 0
	#s.received = 0
}

pred twoStepA[s, s', s'': State]{
	send[s, s']
	receive[s', s'']
}

pred twoStepB[s, s', s'': State]{
	receive[s, s']
	send[s', s'']
}

pred send[s, s': State]{
	some p: Packet | (p in Sender.(s.toSend)) and (p in Channel.(s'.inTransit)) and
		(Sender.(s'.toSend) =( Sender.(s.toSend) - p)) and 
		(Channel.(s'.inTransit) = (Channel.(s.inTransit) + p)) and
		(Receiver.(s'.received) = Receiver.(s.received))
}

pred receive[s, s': State]{
	some p: Packet | (p in Channel.(s.inTransit)) and (p in Receiver.(s'.received)) and
		(Channel.(s'.inTransit) =( Channel.(s.inTransit) - p)) and 
		(Receiver.(s'.received) = (Receiver.(s.received) + p)) and
		(Sender.(s'.toSend) = Sender.(s.toSend))
}

pred show{
	some State
}

pred traceTwoStep{
	init[first]
	all s: State - (last + last.prev) | let s' = s.next | let s'' = s'.next |  
		twoStepA[s, s', s''] or twoStepB[s, s', s'']
}

run show

run trace for 11

run traceTwoStep for 11


//unused
pred trace{
	init[first]
	all s: State - last | let s' = s.next | step[s, s']
}

//unused
pred step[s, s': State]{
	send[s, s'] or receive[s, s']
}

//Doesn't Work
pred both[s, s': State]{
	some p, q: Packet | (p in Sender.(s.toSend)) and (p in Channel.(s'.inTransit)) and
		(Sender.(s'.toSend) =( Sender.(s.toSend) - p)) and 
		(Channel.(s'.inTransit) = (Channel.(s.inTransit) + p)) and
		
		(q in Channel.(s.inTransit)) and (q in Receiver.(s'.received)) and
		(Channel.(s'.inTransit) =( Channel.(s.inTransit) - q)) and 
		(Receiver.(s'.received) = (Receiver.(s.received) + q)) 
}
