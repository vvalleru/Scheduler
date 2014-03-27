module planning

abstract sig Node {
	disj nextSiblingC, firstChildC: lone Choice,
	disj nextSiblingP, firstChildP: lone Parallel,
	disj nextSiblingT, firstChildT: lone Try,
	disj nextSiblingS, firstChildS: lone Sequential,
	disj nextSiblingLeaf, firstChildLeaf: lone Leaf,

	child: set Node,
	sibling: set Node,
	subtree: set Node
//	immediateChildren : set Node
}

abstract sig Choice extends Node {}
abstract sig Parallel extends Node {}
abstract sig Try extends Node {}
abstract sig Sequential extends Node {}
abstract sig Leaf extends Node{}

one sig Process{
	root: one Node
}

fact processNoCycles{
	//there are no cycles in the process tree
//	all n:Choice | n !in n.subtree and n !in n.^sibling
//	all n:Try | n !in n.subtree and n !in n.^sibling
//	all n:Parallel | n !in n.subtree and n !in n.^sibling
//	all n:Sequential | n !in n.subtree and n !in n.^sibling
//	all n:Node | n !in n.subtree and n !in n.^sibling
	all n:Node | n !in n.subtree
//TODO leaves can still be siblings of themselves, need to fix this!
}

fact processConnected{
	Node = Process.root.*subtree
}

one sig Sched {
	header: some SchedEl
}

sig SchedEl {
	nextEl: set SchedEl,
	ref: one Leaf
}

fact scheduleNoCycles{
	//there are no cycles in the schedule
	all n:SchedEl | n !in n.^nextEl
}

fact scheduleConnected{
	SchedEl = Sched.header.*nextEl
}

fact scheduleDistinctRefs{
	//no SchedEl can share a Leaf ref
	all t, t': SchedEl | t.ref = t'.ref => t = t'
}

fact nodeChildUnion{
	all n:Node | n.child=(n.firstChildC + n.firstChildP + n.firstChildT + n.firstChildS + n.firstChildLeaf)
}

fact nodeSiblingUnion{
	all n:Node | n.sibling=(n.nextSiblingC + n.nextSiblingP + n.nextSiblingT + n.nextSiblingS + n.nextSiblingLeaf)
}

fact nodeSubtree{
	//the subtree of a Leaf is itself
//	all l:Leaf | l.subtree=l
	all l:Leaf | no l.subtree
	//the subtree of a non-Leaf node is all of its descendents and does not include itself or siblings
	all n:Choice | n.subtree=(n.child.*sibling + (n.child.*sibling).subtree)
	all n:Try | n.subtree=(n.child.*sibling + (n.child.*sibling).subtree)
	all n:Parallel | n.subtree=(n.child.*sibling + (n.child.*sibling).subtree)
	all n:Sequential | n.subtree=(n.child.*sibling + (n.child.*sibling).subtree)
}

fact nodeDistinctPointers{
	//no nodes can share a child
	no disj n, n' : Node | some n.child & n'.child
}

fact nodeNumberOfChildren{
	//any intermediate node must have a child
	all n:Choice | #n.child=1
	all n:Try | #n.child=1
	all n:Parallel | #n.child=1
	all n:Sequential | #n.child=1
	//a leaf node cannot have a child
	all n:Leaf | no n.child
}

fact nodeNumberOfSiblings{
	//any node can only point to zero or one siblings
	all n:Node | #n.sibling < 2
}

fact nodeNoCycles{
//	all m,n:(Node-Leaf) | m in n.subtree => m !in n.^sibling
//	all m,n:(Node-Leaf) | m in n.^sibling => m !in n.subtree
	all m,n:Node | m in n.subtree => m !in n.^sibling
	all m,n:Node | m in n.^sibling => m !in n.subtree
}

fact scheduleChoice{
	//only one Choice child is in the schedule (but can be multiple leaves if nested)
	all n:Choice, l,l':Leaf | 
		l in n.child.*sibling and 
		l' in n.child.*sibling and 
		l in Sched.header.*nextEl.ref and 
		l' in Sched.header.*nextEl.ref => l=l'
	all n:Choice, m,m':Node, l,l':Leaf |
		(m in n.subtree and
		l in m.subtree and
		l in Sched.header.*nextEl.ref and
		m' in n.subtree and 
		l' in m'.subtree and 
		l' in Sched.header.*nextEl.ref) => (m=m' or m in m'.subtree or m' in m.subtree)
}

fact scheduleTry{
	//the first Try child is always in the schedule (can be multiple leaves if nested)
	all n:Try, l,l':Leaf | 
		l in n.child.*sibling and
		l' in n.child.*sibling and 
		l in Sched.header.*nextEl.ref and 
		l' in Sched.header.*nextEl.ref => l=l'
	all n:Try, m,m':Node, l,l':Leaf | 
		(m in n.subtree and
		l in m.subtree and
		l in Sched.header.*nextEl.ref and
		m' in n.subtree and 
		l' in m'.subtree and 
		l' in Sched.header.*nextEl.ref) => (m=m' or m in m'.subtree or m' in m.subtree)
}

fact forceInclude{
	//all immediate Leaf children are in schedule for Parallel and Sequential
	all n:Parallel, l:Leaf | l in n.child.*sibling => l in Sched.header.*nextEl.ref
	all n:Sequential, l:Leaf | l in n.child.*sibling => l in Sched.header.*nextEl.ref
}
fact scheduleElementParallel{
	//any immediate or nested leftmost children can be done simultaneously
	//immediate...
	all n:Parallel, l,l':Leaf, s,s':SchedEl | 
		l in n.child.*sibling and 
		l' in n.child.*sibling and 
		l in s.ref and l' in s'.ref and
		s in Sched.header => s' in Sched.header
	//nested...
	all n:Parallel, p,q:Node, l,l':Leaf, s,s':SchedEl | 
		p in (n+n.subtree) and 
		q in (n+n.subtree) and 
		(l in p.child or l in n.child.*sibling) and 
		(l' in q.child or l' in n.child.*sibling) and 
		l in s.ref and l' in s'.ref and
		s in Sched.header => s' in Sched.header
	all n:Parallel, p,q:Node, l,l':Leaf, s,s',f:SchedEl | 
		p in (n+n.subtree) and 
		q in (n+n.subtree) and 
		(l in p.child or l in n.child.*sibling) and 
		(l' in q.child or l' in n.child.*sibling) and 
		l in s.ref and l' in s'.ref and
		s in f.nextEl => s' in f.nextEl
	//if there is a multiple header, only leaves of parallel nodes can be in it
	all l,l':Leaf | 
		l in Sched.header.ref and 
		l' in Sched.header.ref and 
		(l != l') => l in Parallel.subtree and l' in Parallel.subtree
	all s,s':SchedEl | 
		s in Sched.header and s' in s.^nextEl => s' !in Sched.header
	//if there is a multiple nextEl, only leaves of parallel nodes can be in it
	all l,l':Leaf, p:SchedEl | 
		l in p.nextEl.ref and 
		l' in p.nextEl.ref and 
		(l != l') => l in Parallel.subtree and l' in Parallel.subtree
}

fact scheduleSequential{
	//all children are in the schedule in sequential order
	all n:Sequential, p,q:Node, l,l':Leaf, s,s':SchedEl | 
		p in n.child.*sibling and q in p.^sibling and
		l in p.subtree and l' in q.subtree and
		l in s.ref and
		l' in s'.ref => s' in s.^nextEl
}

pred show(){
//	#(Parallel.child.*sibling) > 2
}
run show for 5 but exactly 2 Parallel
