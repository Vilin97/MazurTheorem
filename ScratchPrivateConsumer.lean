import ScratchPrivateProducer

example (n : Nat) (h : n + 1 = 3) : n + 1 = 3 := by
  exact ScratchPrivateProducer.value n h
