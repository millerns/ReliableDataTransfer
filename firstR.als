open util/ordering[State]
	
lone sig Sender{}

lone sig Receiver{}

sig State{
	toSend: set Packet,
//	sent: set Packet,
	received: set Packet,
	inTransit: set Packet
}

sig RelatedState{
	toSend: Sender lone -> set Packet
	inTransit: Channel lone -> set Packet
	received: Receiver lone -> set Packet
}

pred initR[s: RelatedState]{
	all p: Packet | p in Sender.(s.toSend)
	#s.toSend = 5
	#s.inTransit = 0
	#s.received = 0
}
