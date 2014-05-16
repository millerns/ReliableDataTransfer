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
//represents the one to one unique relationship between data and checksum
one sig checkRelData{
	rel: Data one -> one Checksum
}
fact relData{ all d: Data| all c: Checksum|  #(checkRelData.rel).c = 1 and 
		 #d.(checkRelData.rel) = 1
}

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
//represents a transition where ACK was sent from receiver
pred replyACK[s, s': State]{
	one a : ACK| #s.inTransit=0 and a = (Channel.(s'.inTransit)).payload and 
		s'.received = s.received and s'.toSend = s.toSend
}
//represents a transition where NAK was sent from receiver
pred replyNAK[s, s': State]{
	one n : NAK| #s.inTransit=0 and n = (Channel.(s'.inTransit)).payload and 
	s'.toSend = s.toSend
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
	#Checksum = #Data
	//Nothing is being sent
	#s.inTransit = 0
	//Nothing has been received
	#s.received = 0
}
//Forces no corrupt data
pred force0Corrupt{
	all p1: Packet| all p2: Packet - p1|  p1.payload != p2.payload
	all p: Packet| calcChecksum[p.payload] = p.ch
	#Packet = #Data
	#last.received = 5
}
//Forces 1 corrupt data and guaruntees all are received
pred force1CorruptSucceed{
	#Packet = 8
	#last.received = 5
	one p: Packet| all o: Packet - p| calcChecksum[o.payload] = o.ch and calcChecksum[p.payload] != p.ch
}
//Forces 1 corrupt data and ensures failure
pred force1CorruptFail{
	#Packet = 8
	#last.received !=5
	one p: Packet| all o: Packet - p| calcChecksum[o.payload] = o.ch and calcChecksum[p.payload] != p.ch
	skip[last.prev,last]
}

//Perform a send followed by a receive OR Perform skips
pred threeStepA[s, s', s'', s''': State]{
	firstSend[s, s'] or ackSend[s, s'] or nakSend[s,s'] or (skip[s, s'] and skip[s',s''] and skip [s'',s'''])
	receive[s', s'', s'''] or (skip[s, s'] and skip[s',s''] and skip [s'',s'''])
}

//Perform a receive followed by a send OR a skip
pred threeStepB[s, s', s'', s''': State]{
	receive[s, s', s'']
	ackSend[s'', s'''] or nakSend[s'',s'''] or skip[s'',s''']
}

//Perform a receive followed by a send OR a skip
pred threeStepC[s,s',s'': State]{
	receive[s.prev, s, s']
	ackSend[s', s''] or nakSend[s',s''] or skip[s', s'']
}

//forces nothing to change
pred skip[s, s': State]{
	one n:NAK+ACK| (Channel.(s.inTransit)).payload=n and s.toSend = s'.toSend and
		s.inTransit = s'.inTransit and s.received = s'.received and 
		(Channel.(s.inTransit)).ch != calcChecksum[n]
}

//Send an instance of data by removing it from the list of data
//to send and placing it in a Packet which is placed inTransit
pred firstSend[s, s': State]{
	one d: Sender.(s.toSend) | one p: Packet | Sender.(s'.toSend) = Sender.(s.toSend) - d and
		Channel.(s'.inTransit) = p and #Channel.(s.inTransit) = 0 and 
		(Channel.(s'.inTransit)).payload = d and s.received = s'.received
}

//Transition to send data from the sender when fed an ACK
pred ackSend[s, s': State]{
	one d: Sender.(s.toSend) | one p: Packet | let t = (Channel.(s.inTransit)).payload| 
		Sender.(s'.toSend) = Sender.(s.toSend) - d and
		Channel.(s'.inTransit) = p and t in ACK  and 
		(Channel.(s'.inTransit)).payload = d and s.received = s'.received and 
		calcChecksum[t] = (Channel.(s.inTransit)).ch
}

//function to get the last data sent
fun lastSent[s: State] : one Data{
	(Channel.((s.prev.prev).inTransit)).payload
}
//transition to send data from sender when fed a NAK
pred nakSend[s, s': State]{
	let d = lastSent[s]| one p: Packet | let t= (Channel.(s.inTransit)).payload |
		 s.toSend = s'.toSend and p.payload = d and
		Channel.(s'.inTransit) = p and t in NAK  and 
		s.received = s'.received and p.ch = calcChecksum[d] and
		calcChecksum[t] = (Channel.(s.inTransit)).ch
}


//Receive an instance of data by removing it from the list of
//Packets in transit and placing it in the list of received data
//and replying with an ack
//OR
//Receive an instance of data that has been corrupted and
//reply with a NAK
pred receive[s, s', s'': State]{
	one p: Channel.(s.inTransit) |
		(Receiver.(s'.received) = Receiver.(s.received) + p.payload and 
		s.toSend = s'.toSend and replyACK[s', s''] and calcChecksum[p.payload]=p.ch)
		or 
		(Receiver.(s'.received) = Receiver.(s.received) + p.payload and 
		Receiver.(s''.received) = Receiver.(s.received) and
		s.toSend = s'.toSend and replyNAK[s', s''] and calcChecksum[p.payload]!=p.ch)
}

//Trace a successful run of the model
pred traceNoCorruption{
	init[first]
	firstSend[first, first.next]
	force0Corrupt
	//skip[first.next.next.next, first.next.next.next.next]
	all s: ( State-last - last.prev - last.prev.prev) | let s' = s.next | let s'' = s'.next | let s''' = s''.next|
		threeStepA[s, s', s'', s'''] or threeStepB[s,s',s'', s'''] or threeStepC[s,s',s'']
}
//Trace a FAIL run of the model
pred traceOneCorruptFail{
	init[first]
	firstSend[first, first.next]
	force1CorruptFail
	//skip[first.next.next.next, first.next.next.next.next]
	all s: ( State-last - last.prev - last.prev.prev) | let s' = s.next | let s'' = s'.next | let s''' = s''.next|
		threeStepA[s, s', s'', s'''] or threeStepB[s,s',s'', s'''] or threeStepC[s,s',s'']
}
//Trace a successful run of the model with corruption
pred traceOneCorruptSuccess{
	init[first]
	firstSend[first, first.next]
	force1CorruptSucceed
	//skip[first.next.next.next, first.next.next.next.next]
	all s: ( State-last - last.prev - last.prev.prev) | let s' = s.next | let s'' = s'.next | let s''' = s''.next|
		threeStepA[s, s', s'', s'''] or threeStepB[s,s',s'', s'''] or threeStepC[s,s',s'']
}

//16 states
run traceNoCorruption for 16

//8 states (could be more, would hang)
run traceOneCorruptFail for 8

//19 states
run traceOneCorruptSuccess for 19
