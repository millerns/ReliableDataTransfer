open util/ordering[State]

sig State{
	toSend: set Packet,
//	sent: set Packet,
	received: set Packet,
	inTransit: set Packet
}

sig Packet{}

pred init[s: State]{
	all p: Packet | p in s.toSend 
	#s.toSend = 5
//	#s.sent = 0
	#s.received = 0
	#s.inTransit = 0
}

pred trace{
	init[first]
	all s: State - last | let s' = s.next | step[s, s']
}

pred step[s, s': State]{
	(#s.toSend = 0) or sendData[s, s']
	(#s.inTransit = 0) or receiveData[s, s']
}

fact TrinaryPosition{
	all p: Packet, s: State | ((p in s.toSend) and !(p in s.inTransit) and !(p in s.received)) or
		(!(p in s.toSend) and (p in s.inTransit) and !(p in s.received))  or
		(!(p in s.toSend) and !(p in s.inTransit) and (p in s.received)) 
}

fact ReceivedContainment{
	all p: Packet, s: State-last | (p in s.received) => (p in (s.next).received)
}

pred sendData[s, s': State]{
	some p: s.toSend | let r = (s.toSend - p) | (p in s.toSend) and
		(p in s'.inTransit) and (s'.toSend = r)
}

pred receiveData[s, s': State] {
	some p: s.inTransit |  (p in s.inTransit) and !(p in s'.inTransit)
		and !(p in s.received) and (p in s'.received) //and (s'.inTransit = (s.inTransit - p))
	//	and (s'.received = (s.received + p))  //and !(s.received in s'.inTransit)
}

run trace for 8

/*
pred send[s, s': Sender; r,' r: Reciever]{
	p: Packet in s.toSend | !(p in s'.toSend) and
		(p in s'.sent) and (p in r'.recieved)
}

pred send[s: State]{
	let S = s.Sender | let R = s.Reciever |
	p: Packet in S.toSend | 
}
*/
/*
pred step[s, s': State]{
	let S = s.Sender, S' = s'.Sender, R = s'.Reciever |
		let p= Packet in S.toSend | (p in R.recieved) and
		(p in S'.sent)
}
*/
/*
pred sendData[s, s': State]{
	one p: Packet |  (p in s.(sender.toSend)) and !(p in s.(channel.inTransit)) and 
		(p in s'.(channel.inTransit)) and	!(p in s'.(sender.toSend)) and
		(p in s'.(sender.sent))
}

pred recieveData[]{

}

pred step[s, s': State]{
	sendData[s, s']
}

pred trace{
	init[first]
	all s: State - last | let s' = s.next | step[s, s']
	//all s: State - last | let s' = s.next | sendData[s, s']
	//all s: State - last | let s' = s.next | step[s, s']
}
*/
pred show{
	init[first]
	//	some State
}

run show
