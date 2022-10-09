abstract sig Tree {}
sig Nil extends Tree {}
sig Node extends Tree {
    disj left, right : Tree - Root
}
one sig Root extends Node {}

fact {
    no n : Node | n in n.^(left+right)
    all t : Tree - Root | one (left+right).t
}
run {} for 10

assert treeReach {
    all t : Tree | t in Root.*(left+right)
}
check treeReach for 10
