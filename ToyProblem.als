module schedule

abstract sig Node{
//	parent: lone Node
//	children: set Node
	nextSet: set Node
}
sig Intermediate extends Node{
	childrenof: set Node,
	child: one SeqChild
}

sig Choice extends Node{
	children: set Leaf,
   	refInt: set Intermediate
}

sig Sequential extends Node{
	child: one SeqChild
}

sig SeqChild extends Node{
	nextChild, prevChild: lone SeqChild
}

abstract sig Leaf extends Node{
	parent: one Node
}
one sig Sched {
	header: one SchedEl
}

sig SchedEl {
	nextEl: lone SchedEl,
	ref: one Leaf//,
  	//reftwo: one Choice
}

fact NoCycles{
//	all n, n': Node | n' in n.*next => n !in n'.*next
	all n:Sched.header.*nextEl|n !in n.^nextEl
}

fact DistinctLeaves {
	all t, t': SchedEl | t.ref = t'.ref => t = t'
}

fact scheduleConnected{
	SchedEl = Sched.header.*nextEl
	all n:SchedEl | no n.nextEl || n in Sched.header.*nextEl
}

fact scheduleConsistent{
	all n, n':SchedEl | n' = n.nextEl => n'.ref in n.ref.nextSet
}

fact allNodesInSched{
//	Node = SchedEl.ref
	SeqChild = SchedEl.ref.parent || Intermediate = SchedEl.ref.parent
}

fact noSelfNext{
	all n:Node | n !in n.nextSet
}

fact enforcePrecedence{
//	all s: SchedEl | s.ref in M2 => s.^nextEl.ref !in M1
	SchedEl = Sched.header.*nextEl
	all n,m:SchedEl | (n.ref.parent = SeqChild and m.ref.parent = SeqChild and m.ref.parent in n.ref.parent.^nextChild) =>
		m in n.^nextEl
}

fact enforceChoice{
	SchedEl = Sched.header.*nextEl
	all n:SchedEl, m:Choice, c:Node | n.ref in m.children and c in m.children and n.ref != c => n.^nextEl.ref != c
}
fact noLeafNext{
	all n:Leaf | no n.nextSet
}
sig M1, M2 extends Intermediate{}
sig M extends Choice{
//	M.children = {M1,M2}
}
//one sig A1, A2 extends M1{}
//one sig A3, A4 extends M2{}

pred empty(){}

run empty for 4
