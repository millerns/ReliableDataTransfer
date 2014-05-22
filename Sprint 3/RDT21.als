open util/ordering[State]

//represents the Sender of data
lone sig Sender{}
//represents the Channel that data travels through when sent
lone sig Channel{}
//represents the Receiver of the data
lone sig Receiver{}
//each data has a checksum
sig Checksum{}
//represents the data that we are trying to send
sig Data{}
//represents acknowledgement data
one sig ACK, NAK extends Data{}
//Sequence bits
abstract sig Sequence{}
one sig on extends Sequence{}
one sig off extends Sequence{}
//represents the one to one unique relationship between data and checksum
one sig checkRelData{
	rel: Data one -> one Checksum
}{#Checksum = #Data}
//represents the containers of data during transfer
sig Packet{
	se: one Sequence,
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
	//Sender keeps track of the last thing to be sent
	lastSent: lone Packet
}
fun calcChecksum[d: Data]  : one Checksum{
	d.(checkRelData.rel)
}
//Sets the initial status of the model
pred init[s: State]{
	//All data is in the list of data (Not nak or ack) to be sent
	all d: (Data-ACK-NAK) | d in Sender.(s.toSend)
	no d: ACK+NAK | d in Sender.(s.toSend)
	//5 instances of data exist
	#s.toSend = 5
	//Nothing is being sent
	#s.inTransit = 0
	//Nothing has been received
	#s.received = 0
	#s.lastSent = 0
}
//Forces no corrupt data
pred force0Corrupt{
	all p: Packet| calcChecksum[p.payload] = p.ch
	#last.received = #(Data - ACK - NAK)
	#Packet = #Data
}
//Forces 1 corrupt data and guaruntees all are received
pred force1CorruptSucceed{
	#Packet = #Data + 1
	#last.received = #(Data - ACK - NAK)
	calcChecksum[(Channel.(last.inTransit)).payload] = (Channel.(last.inTransit)).ch
	let p =(Channel.(first.next.next.next.inTransit))| p.payload in NAK and p.ch != calcChecksum[p.payload]
}
//Send an instance of data by removing it from the list of data
//to send and placing it in a Packet which is placed inTransit
pred firstSend[s, s': State]{
	one d: Sender.(s.toSend) | one p: Packet | Sender.(s'.toSend) = Sender.(s.toSend) - d and
		Channel.(s'.inTransit) = p and #Channel.(s.inTransit) = 0 and 
		(Channel.(s'.inTransit)).payload = d and s.received = s'.received and s'.lastSent = p
		and p.se = off
}

fun flipBit[s: State] : one Sequence{
	Sequence - (s.lastSent).se
}
//Transition to send data from the sender when fed an ACK
pred ackSend[s, s': State]{
	one d: Sender.(s.toSend) | one p: Packet | let t = (Channel.(s.inTransit)).payload| 
		Sender.(s'.toSend) = Sender.(s.toSend) - d and
		Channel.(s'.inTransit) = p and t in ACK  and 
		(Channel.(s'.inTransit)).payload = d and s.received = s'.received and 
		calcChecksum[t] = (Channel.(s.inTransit)).ch and s'.lastSent = p
		and p.se = flipBit[s] or corruptSend[s,s',d,t,p]
}

pred corruptSend[s,s':State, d,t:Data, p:Packet]{
		 s.toSend = s'.toSend and p.payload = d and
		Channel.(s'.inTransit) = p and ((t in ACK) or (t in NAK)) and 
		s.received = s'.received and
		calcChecksum[t] != (Channel.(s.inTransit)).ch and s'.lastSent = p
		and p = s.lastSent and p.se = (s.lastSent).se
}
//function to get the last data sent
//fun lastSent[s: State] : one Data{
	//(Channel.((s.prev.prev).inTransit)).payload
//}
//transition to send data from sender when fed a NAK
pred nakSend[s, s': State]{
	let d = (s.lastSent).payload| one p: Packet | let t= (Channel.(s.inTransit)).payload |
		 s.toSend = s'.toSend and p.payload = d and
		Channel.(s'.inTransit) = p and t in NAK  and 
		s.received = s'.received and
		calcChecksum[t] = (Channel.(s.inTransit)).ch and s'.lastSent = p
		and p.se = (s.lastSent).se or corruptSend[s,s',d,t,p]
}
pred receiveOff[s,s',s'': State]{
	one p: Channel.(s.inTransit) |
		(Receiver.(s'.received) = Receiver.(s.received) + p.payload and 
		s.toSend = s'.toSend and s.lastSent = s'.lastSent and replyACK[s', s''] and 
		calcChecksum[p.payload]=p.ch and p.se = off)
		or 
		(Receiver.(s'.received) = Receiver.(s.received) + p.payload and 
		Receiver.(s''.received) = Receiver.(s.received) and
		s.toSend = s'.toSend and s.lastSent = s'.lastSent and replyNAK[s', s''] and calcChecksum[p.payload]!=p.ch)
		or
		(Receiver.(s'.received) = Receiver.(s.received) and 
		s.toSend = s'.toSend and s.lastSent = s'.lastSent and replyACK[s', s''] and 
		calcChecksum[p.payload]=p.ch and p.se = on)
}
pred receiveOn[s,s',s'': State]{
	one p: Channel.(s.inTransit) |
		(Receiver.(s'.received) = Receiver.(s.received) + p.payload and 
		s.toSend = s'.toSend and s.lastSent = s'.lastSent and replyACK[s', s''] and 
		calcChecksum[p.payload]=p.ch and p.se = on)
		or 
		(Receiver.(s'.received) = Receiver.(s.received) + p.payload and 
		Receiver.(s''.received) = Receiver.(s.received) and
		s.toSend = s'.toSend and s.lastSent = s'.lastSent and replyNAK[s', s''] and calcChecksum[p.payload]!=p.ch)
		or
		(Receiver.(s'.received) = Receiver.(s.received) and 
		s.toSend = s'.toSend and s.lastSent = s'.lastSent and replyACK[s', s''] and 
		calcChecksum[p.payload]=p.ch and p.se = off)
}

//represents a transition where ACK was sent from receiver
pred replyACK[s, s': State]{
	one a : ACK| #s.inTransit=0 and a = (Channel.(s'.inTransit)).payload and 
		s'.received = s.received and s'.toSend = s.toSend and s.lastSent = s'.lastSent
}
//represents a transition where NAK was sent from receiver
pred replyNAK[s, s': State]{
	one n : NAK| #s.inTransit=0 and n = (Channel.(s'.inTransit)).payload and 
	s'.toSend = s.toSend and s.lastSent = s'.lastSent
}

//Perform a send followed by a receive OR Perform skips
pred threeStepAOff[s, s', s'', s''': State]{
	firstSend[s, s'] or ackSend[s,s'] or nakSend[s,s']
	receiveOff[s', s'', s''']
	
}

//Perform a receive followed by a send OR a skip
pred threeStepBOff[s, s', s'', s''': State]{
	receiveOff[s, s', s'']
	ackSend[s'', s'''] or (nakSend[s'',s'''] and receiveOff[s''',s'''.next,s'''.next.next])
}

pred threeStepAOn[s, s', s'', s''': State]{
	ackSend[s,s'] or nakSend[s,s']
	receiveOn[s', s'', s''']
}

//Perform a receive followed by a send OR a skip
pred threeStepBOn[s, s', s'', s''': State]{
	receiveOn[s, s', s'']
	ackSend[s'', s'''] or (nakSend[s'',s'''] and receiveOn[s''',s'''.next,s'''.next.next])
}

pred off[s1,s2,s3,s4,s5: State]{
	threeStepAOff[s1,s2,s3,s4]
	threeStepBOff[s2,s3,s4,s5]
}
pred offToOff[s1,s2,s3,s4,s5: State]{
	threeStepBOff[s1,s2,s3,s4]
	receiveOff[s4,s5,s5.next]
}
pred on[s1,s2,s3,s4,s5: State]{
	threeStepAOn[s1,s2,s3,s4]
	threeStepBOn[s2,s3,s4,s5]
}
pred onToOn[s1,s2,s3,s4,s5: State]{
	threeStepBOn[s1,s2,s3,s4]
	receiveOn[s4,s5,s5.next]
}
pred onToOff[s1,s2,s3,s4,s5: State]{
	threeStepBOn[s1,s2,s3,s4]
	threeStepAOff[s3,s4,s5,s5.next]
}
pred offToOn[s1,s2,s3,s4,s5: State]{
	threeStepBOff[s1,s2,s3,s4]
	threeStepAOn[s3,s4,s5,s5.next]
}
	//		off[s1,s2,s3,s4,s5] or on[s1,s2,s3,s4,s5] or offToOff[s1,s2,s3,s4,s5] or offToOn[s1,s2,s3,s4,s5] or onToOn[s1,s2,s3,s4,s5] or onToOff[s1,s2,s3,s4,s5] 
//Trace a successful run of the model
pred traceNoCorruption{
	init[first]
	force0Corrupt
	//skip[first.next.next.next, first.next.next.next.next]

	all s1: (State - last - last.prev - last.prev.prev - last.prev.prev.prev - last.prev.prev.prev.prev)| let s2 = s1.next| let s3 = s2.next| let s4 = s3.next | let s5 = s4.next|
		off[s1,s2,s3,s4,s5] or on[s1,s2,s3,s4,s5] or offToOn[s1,s2,s3,s4,s5] or offToOn[s1.prev,s1,s2,s3,s4] or onToOff[s1,s2,s3,s4,s5] or onToOff[s1.prev,s1,s2,s3,s4] or offToOff[s1,s2,s3,s4,s5]  or offToOff[s1.prev, s1, s2, s3, s4] or onToOn[s1,s2,s3,s4,s5] or onToOn[s1.prev,s1,s2,s3,s4]
}

//Trace a successful run of the model with corruption
pred traceOneCorruptSuccess{
	init[first]
	force1CorruptSucceed
	//skip[first.next.next.next, first.next.next.next.next]

	all s1: (State - last - last.prev - last.prev.prev - last.prev.prev.prev - last.prev.prev.prev.prev)| let s2 = s1.next| let s3 = s2.next| let s4 = s3.next | let s5 = s4.next|
		off[s1,s2,s3,s4,s5] or on[s1,s2,s3,s4,s5] or offToOn[s1,s2,s3,s4,s5] or offToOn[s1.prev,s1,s2,s3,s4] or onToOff[s1,s2,s3,s4,s5] or onToOff[s1.prev,s1,s2,s3,s4] or offToOff[s1,s2,s3,s4,s5]  or offToOff[s1.prev, s1, s2, s3, s4] or onToOn[s1,s2,s3,s4,s5] or onToOn[s1.prev,s1,s2,s3,s4]
}

//16 states
run traceNoCorruption for 16

//19 states
run traceOneCorruptSuccess for 22
