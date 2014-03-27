module tree

one sig BinaryTree {
  root: lone Node
}

sig Node {
  left, right: lone Node
}

pred Acyclic(t: BinaryTree) {
  all n: t.root.*(left + right) {
    n !in n.^(left + right)
   // no n.(left) & n.(right)
   lone n.~(left + right)
  }
}

fact NoDisconnectedNodes { 
  BinaryTree.root.*(left + right) = Node
}

run Acyclic for 3
