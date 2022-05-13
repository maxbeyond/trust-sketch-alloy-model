open util/boolean
open util/integer

enum ProgramPostion { EnclaveProgram, HostProgram }
enum MemoryType { EnclaveMemory, SecureMemory, HostMemory }
enum Security { Safe, Compromised }

one sig Attacker {
  rootAccess: Bool
}

sig Program {
  programPostion: ProgramPostion,
  codeAttest: Bool,
  bootSecurity: Security,
  runSecurity: Security
}

sig Memory {
  memoryType: MemoryType,
  security: Security
}

sig Data {}
sig Packet {
  hdr: one Data
}

sig DatapathPkt extends Packet {}

// sent/recv denotes whether the packet is successfully sent or received
one sig HeartBeatPkt extends Packet {
  sent: Bool,
  recv: Bool
}
one sig AckPkt extends Packet {
  sent: Bool,
  recv: Bool
}

// Sketch  <-  incoming  <-  NIC
// Sketch  ->  outgoing  ->  NIC
one sig Sketch {
  program: one Program,
  counter: one Memory,
  heap: one Memory,
  incomingPackets: seq Packet,
  outgoingPackets: seq Packet
}

one sig NIC {
  incomingPackets: seq Packet,
  outgoingPackets: seq Packet
}

one sig PacketsBuffer in Memory {}

sig MyString {}
sig TrafficSummary {
  input: seq Packet,
  counter: one Int,
  hash: one MyString
}

one sig EnclaveChecker {
  inSummary: TrafficSummary,
  outSummary: TrafficSummary
}

one sig NICChecker {
  inSummary: TrafficSummary,
  outSummary: TrafficSummary
}

// if no attacker, assume program and memory are safe
fact {
  (Attacker.rootAccess = False) => {
    all p: Program | p.runSecurity = Safe
    all m: Memory | m.security = Safe
  }
}

// packets
// 1. sent by VM 
// 2. received from network (datapath)
// 3. heartbeat or ack pkt
fact {
  // all Packet instances are used in model
  HeartBeatPkt + AckPkt + DatapathPkt = Packet
  
  // no useless DatapathPkt
  all p: DatapathPkt | (p in NIC.incomingPackets.elems) || (p in Sketch.outgoingPackets.elems)
}

// if plain system, no heartbeat/ack packets
fact NoHeartbeat {
  all p: NIC.incomingPackets.elems | (p in DatapathPkt)
  all p: NIC.outgoingPackets.elems | (p in DatapathPkt)
  all p: Sketch.incomingPackets.elems | (p in DatapathPkt)
  all p: Sketch.outgoingPackets.elems | (p in DatapathPkt)
}

// no duplicate packets in sequence
// we use distinct Packet instance for input integrity check
fact NoDupPkt {
  !(NIC.incomingPackets.hasDups)
  !(NIC.outgoingPackets.hasDups)
  !(Sketch.incomingPackets.hasDups)
  !(Sketch.outgoingPackets.hasDups)

  // easy to check: 'NIC incoming pkts' and 'sketch outgoing pkts' has no overlap
  all p: NIC.incomingPackets.elems | !(p in Sketch.outgoingPackets.elems)
  all p: Sketch.outgoingPackets.elems | !(p in NIC.incomingPackets.elems)
}

// all Memory and Program instances are used in model
fact {
  Sketch.program = Program
  Sketch.counter + Sketch.heap + PacketsBuffer = Memory
}

// pkt stream is not changed if PacketsBuffer is safe
// assume no packet drop due to buffer overflow
fact {
  (PacketsBuffer.security = Safe) => {
    Sketch.incomingPackets = NIC.incomingPackets
    NIC.outgoingPackets = Sketch.outgoingPackets
  }
}

// code attestation can guarantee boot security
fact {
  all p: Program | (p.codeAttest = True) => (p.bootSecurity = Safe)
}

// enclave safety guarantee
fact {
  // remote attestation can be used for code in enclave
  all p: Program | (p.programPostion = EnclaveProgram) => (p.codeAttest = True)

  // code and memory in enclave are safe
  all p: Program | (p.programPostion = EnclaveProgram) => (p.runSecurity = Safe)
  all m: Memory | (m.memoryType = EnclaveMemory) => (m.security = Safe)
}

// strawman (code attestation) only guarantee boot security
fact {
  all p: Program | (p.codeAttest = True) => (p.bootSecurity = Safe)
}

// strawman (secure memory) only guarantee memory are safe
fact {
  all m: Memory | (m.memoryType = SecureMemory) => (m.security = Safe)
}

pred ComputeIntegrity [] {
  Sketch.program.bootSecurity = Safe
  Sketch.program.runSecurity = Safe
}

pred MemoryIntegrity [] {
  Sketch.counter.security = Safe
  Sketch.heap.security = Safe
}

pred InputIntegrity[] {
  Sketch.incomingPackets = NIC.incomingPackets
  Sketch.outgoingPackets = NIC.outgoingPackets
}

pred TrustedSketch[] {
  ComputeIntegrity[]
  MemoryIntegrity[]
  InputIntegrity[]
}

// plain system : sketch is running in host memory
pred PlainSystem[] {
  Sketch.program.programPostion = HostProgram
  Sketch.counter.memoryType = HostMemory
  Sketch.heap.memoryType = HostMemory
  PacketsBuffer.memoryType = HostMemory
}

pred attackerHasRootAccess[] {
  Attacker.rootAccess = True
}

pred ComputeAttack[] {
  Sketch.program.bootSecurity = Compromised
  Sketch.program.runSecurity = Compromised
}

pred UseComputeAttackOnPlain {
  attackerHasRootAccess[] && PlainSystem[]
  && ComputeAttack[] && (!ComputeIntegrity[])
}
run UseComputeAttackOnPlain for 10

pred CounterAttack[] {
  Sketch.counter.security = Compromised
}

pred UseCounterAttackOnPlain {
  attackerHasRootAccess[] && PlainSystem[]
  && CounterAttack[] && (!MemoryIntegrity[])
}
run UseCounterAttackOnPlain for 10

pred HeapAttack[] {
  Sketch.heap.security = Compromised
}

pred UseHeapAttackOnPlain {
  attackerHasRootAccess[] && PlainSystem[]
  && HeapAttack[] && (!MemoryIntegrity[])
}
run UseHeapAttackOnPlain for 10

// inject packets
pred InjectAttack[] {
  some p: Sketch.incomingPackets.elems | !(p in NIC.incomingPackets.elems)
  some p: NIC.outgoingPackets.elems | !(p in Sketch.outgoingPackets.elems)

  all p: NIC.incomingPackets.elems | p in Sketch.incomingPackets.elems
  all p: Sketch.outgoingPackets.elems | p in NIC.outgoingPackets.elems
}

pred UseInjectAttackOnPlain {
  attackerHasRootAccess[] && PlainSystem[]
  && InjectAttack[] && (!InputIntegrity[])
}
run UseInjectAttackOnPlain for 10

// drop packets
pred DropAttack[] {
  some p: NIC.incomingPackets.elems | !(p in Sketch.incomingPackets.elems)
  some p: Sketch.outgoingPackets.elems | !(p in NIC.outgoingPackets.elems)
}

pred UseDropAttackOnPlain {
  attackerHasRootAccess[] && PlainSystem[]
  && DropAttack[] && (!InputIntegrity[])
}
run UseDropAttackOnPlain for 10

pred ModifyPS[PS1: seq Packet, PS2: seq Packet] {
  (#PS1) = (#PS2)
  // all i: Int | (lt[i, #PS1] && gte[i, 0]) => (PS1[i] != PS2[i])
  PS1.elems != PS2.elems
}

// modify outgoing packets
pred ModifyAttack[] {
  ModifyPS[NIC.incomingPackets, Sketch.incomingPackets]
  ModifyPS[NIC.outgoingPackets, Sketch.outgoingPackets]
}

pred UseModifyAttackOnPlain {
  attackerHasRootAccess[] && PlainSystem[]
  && ModifyAttack[] && (!InputIntegrity[])
}
run UseModifyAttackOnPlain for 10


// plain system would be compromised if attacker has root access
assert PlainSystemFail {
  (attackerHasRootAccess[] && PlainSystem[]) => 
    (TrustedSketch[])
}
check PlainSystemFail for 10

// Idea 1: use enclave
pred UseEnclave[] {
  Sketch.program.programPostion = EnclaveProgram
  Sketch.counter.memoryType = EnclaveMemory
  Sketch.heap.memoryType = EnclaveMemory
  PacketsBuffer.memoryType = HostMemory
}

// we use timeout mechanism to make sure at least one heartbeat will get ack packet
// here we model only one heartbeat/ack packet
// we can guarantee that input integrity for all packets before heartbeat/ack
pred SendHeartBeat[] {
  HeartBeatPkt.sent = True
}
pred RecvAckPacket[] {
  AckPkt.recv = True
}

pred EnclaveReplyAck[] {
  // enclave would reply ack after receiving heartbeat pkt
  (HeartBeatPkt.recv = True) => (AckPkt.sent = True)

  // enclave only send ack after receiving heartbeat pkt
  (AckPkt.sent = True) => (HeartBeatPkt.recv = True)
}

fact HeartbeatSentRecv {
  // recv is true only when send is true
  // we use nounce-based HMAC, so heartbeat/ack packet could not be fabricated
  (HeartBeatPkt.recv = True) => (HeartBeatPkt.sent = True)
  (AckPkt.recv = True) => (AckPkt.sent = True)
}

fact TrafficSummaryInput {
  EnclaveChecker.inSummary.input = Sketch.incomingPackets
  EnclaveChecker.outSummary.input = Sketch.outgoingPackets
  NICChecker.inSummary.input = NIC.incomingPackets
  NICChecker.outSummary.input = NIC.outgoingPackets
}

pred IntegrityCheck[t1, t2: TrafficSummary] {
  // checker will check two things
  t1.counter = t2.counter
  t1.hash = t2.hash

  // crypto hash will guarantee following
  (t1.counter = t2.counter && t1.hash = t2.hash) => (t1.input = t2.input)
}

// Idea 2: epoch check
pred EpochCheck[] {
  // traffic summary exchange
  SendHeartBeat[]
  RecvAckPacket[]
  EnclaveReplyAck[]

  IntegrityCheck[EnclaveChecker.inSummary, NICChecker.inSummary]
  IntegrityCheck[EnclaveChecker.outSummary, NICChecker.outSummary]
}

pred OurSystem[] {
  UseEnclave[]
  EpochCheck[]
}

assert UseComputeAttackOnOurSys {
  (attackerHasRootAccess[] && OurSystem[]) => !(ComputeAttack[])
}
check UseComputeAttackOnOurSys for 10

assert UseCounterAttackOnOurSys {
  (attackerHasRootAccess[] && OurSystem[]) => !(CounterAttack[])
}
check UseCounterAttackOnOurSys for 10

assert UseHeapAttackOnOurSys {
  (attackerHasRootAccess[] && OurSystem[]) => !(HeapAttack[])
}
check UseHeapAttackOnOurSys for 10

assert UseInjectAttackOnOurSys {
  (attackerHasRootAccess[] && OurSystem[]) => !(InjectAttack[])
}
check UseInjectAttackOnOurSys for 10

assert UseDropAttackOnOurSys {
  (attackerHasRootAccess[] && OurSystem[]) => !(DropAttack[])
}
check UseDropAttackOnOurSys for 10

assert UseModifyAttackOnOurSys {
  (attackerHasRootAccess[] && OurSystem[]) => !(ModifyAttack[])
}
check UseModifyAttackOnOurSys for 10

// Idea 1/2/3 will ensure trust sketch
assert OurSystemCorrect {
  (attackerHasRootAccess[] 
    && OurSystem[]) => 
      (TrustedSketch[])
}
check OurSystemCorrect for 10 but 4 Int

// Generate a sample instance of the model
pred simulate {
  attackerHasRootAccess[] 
  OurSystem[]
  TrustedSketch[]
}
// assume we have some in/out packets
run simulate for 10

