namespace ScratchPrivateProducer

private def f (n : Nat) : Nat := n + 1

theorem value (n : Nat) (h : f n = 3) : f n = 3 := h

end ScratchPrivateProducer
