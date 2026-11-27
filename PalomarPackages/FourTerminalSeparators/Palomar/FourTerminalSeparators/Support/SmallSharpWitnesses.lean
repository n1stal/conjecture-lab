module

public import Palomar.FourTerminalSeparators.Support.SharpSmallModel

@[expose] public section

namespace HakKozerenkoSeparatorGraph

def model6 : SmallGraphData 4 where
  edge := boolEdge #v[14,13,11,7]
  dist := rowTable #v[#v[0,1,1,1],#v[1,0,1,1],#v[1,1,0,1],#v[1,1,1,0]]
  next := fun a b => ⟨rowTable #v[#v[0,1,2,3],#v[0,1,2,3],#v[0,1,2,3],#v[0,1,2,3]] a b, by
    have H : ∀ (a b : Fin 4), rowTable #v[#v[0,1,2,3],#v[0,1,2,3],#v[0,1,2,3],#v[0,1,2,3]] a b < 4 := by decide +kernel
    exact H a b⟩
  symm := by decide +kernel
  noloop := by decide +kernel
  zero := by decide +kernel
  triangle := by decide +kernel
  edgeBound := by decide +kernel
  nextOK := by decide +kernel

theorem low_attains_6 : VertexAttains 6 := by
  apply model6.attains 0 1 2 3
  · constructor <;> decide
  · decide +kernel
  · decide


def model7 : SmallGraphData 4 where
  edge := boolEdge #v[12,12,11,7]
  dist := rowTable #v[#v[0,2,1,1],#v[2,0,1,1],#v[1,1,0,1],#v[1,1,1,0]]
  next := fun a b => ⟨rowTable #v[#v[0,2,2,3],#v[2,1,2,3],#v[0,1,2,3],#v[0,1,2,3]] a b, by
    have H : ∀ (a b : Fin 4), rowTable #v[#v[0,2,2,3],#v[2,1,2,3],#v[0,1,2,3],#v[0,1,2,3]] a b < 4 := by decide +kernel
    exact H a b⟩
  symm := by decide +kernel
  noloop := by decide +kernel
  zero := by decide +kernel
  triangle := by decide +kernel
  edgeBound := by decide +kernel
  nextOK := by decide +kernel

theorem low_attains_7 : VertexAttains 7 := by
  apply model7.attains 0 1 2 3
  · constructor <;> decide
  · decide +kernel
  · decide


def model8 : SmallGraphData 4 where
  edge := boolEdge #v[10,5,10,5]
  dist := rowTable #v[#v[0,1,2,1],#v[1,0,1,2],#v[2,1,0,1],#v[1,2,1,0]]
  next := fun a b => ⟨rowTable #v[#v[0,1,1,3],#v[0,1,2,0],#v[1,1,2,3],#v[0,0,2,3]] a b, by
    have H : ∀ (a b : Fin 4), rowTable #v[#v[0,1,1,3],#v[0,1,2,0],#v[1,1,2,3],#v[0,0,2,3]] a b < 4 := by decide +kernel
    exact H a b⟩
  symm := by decide +kernel
  noloop := by decide +kernel
  zero := by decide +kernel
  triangle := by decide +kernel
  edgeBound := by decide +kernel
  nextOK := by decide +kernel

theorem low_attains_8 : VertexAttains 8 := by
  apply model8.attains 0 1 2 3
  · constructor <;> decide
  · decide +kernel
  · decide


def model9 : SmallGraphData 4 where
  edge := boolEdge #v[14,1,1,1]
  dist := rowTable #v[#v[0,1,1,1],#v[1,0,2,2],#v[1,2,0,2],#v[1,2,2,0]]
  next := fun a b => ⟨rowTable #v[#v[0,1,2,3],#v[0,1,0,0],#v[0,0,2,0],#v[0,0,0,3]] a b, by
    have H : ∀ (a b : Fin 4), rowTable #v[#v[0,1,2,3],#v[0,1,0,0],#v[0,0,2,0],#v[0,0,0,3]] a b < 4 := by decide +kernel
    exact H a b⟩
  symm := by decide +kernel
  noloop := by decide +kernel
  zero := by decide +kernel
  triangle := by decide +kernel
  edgeBound := by decide +kernel
  nextOK := by decide +kernel

theorem low_attains_9 : VertexAttains 9 := by
  apply model9.attains 0 1 2 3
  · constructor <;> decide
  · decide +kernel
  · decide


def model10 : SmallGraphData 4 where
  edge := boolEdge #v[2,5,10,4]
  dist := rowTable #v[#v[0,1,2,3],#v[1,0,1,2],#v[2,1,0,1],#v[3,2,1,0]]
  next := fun a b => ⟨rowTable #v[#v[0,1,1,1],#v[0,1,2,2],#v[1,1,2,3],#v[2,2,2,3]] a b, by
    have H : ∀ (a b : Fin 4), rowTable #v[#v[0,1,1,1],#v[0,1,2,2],#v[1,1,2,3],#v[2,2,2,3]] a b < 4 := by decide +kernel
    exact H a b⟩
  symm := by decide +kernel
  noloop := by decide +kernel
  zero := by decide +kernel
  triangle := by decide +kernel
  edgeBound := by decide +kernel
  nextOK := by decide +kernel

theorem low_attains_10 : VertexAttains 10 := by
  apply model10.attains 0 1 2 3
  · constructor <;> decide
  · decide +kernel
  · decide


def model11 : SmallGraphData 5 where
  edge := boolEdge #v[30,5,3,1,1]
  dist := rowTable #v[#v[0,1,1,1,1],#v[1,0,1,2,2],#v[1,1,0,2,2],#v[1,2,2,0,2],#v[1,2,2,2,0]]
  next := fun a b => ⟨rowTable #v[#v[0,1,2,3,4],#v[0,1,2,0,0],#v[0,1,2,0,0],#v[0,0,0,3,0],#v[0,0,0,0,4]] a b, by
    have H : ∀ (a b : Fin 5), rowTable #v[#v[0,1,2,3,4],#v[0,1,2,0,0],#v[0,1,2,0,0],#v[0,0,0,3,0],#v[0,0,0,0,4]] a b < 5 := by decide +kernel
    exact H a b⟩
  symm := by decide +kernel
  noloop := by decide +kernel
  zero := by decide +kernel
  triangle := by decide +kernel
  edgeBound := by decide +kernel
  nextOK := by decide +kernel

theorem low_attains_11 : VertexAttains 11 := by
  apply model11.attains 1 2 3 4
  · constructor <;> decide
  · decide +kernel
  · decide


def model12 : SmallGraphData 5 where
  edge := boolEdge #v[30,1,1,1,1]
  dist := rowTable #v[#v[0,1,1,1,1],#v[1,0,2,2,2],#v[1,2,0,2,2],#v[1,2,2,0,2],#v[1,2,2,2,0]]
  next := fun a b => ⟨rowTable #v[#v[0,1,2,3,4],#v[0,1,0,0,0],#v[0,0,2,0,0],#v[0,0,0,3,0],#v[0,0,0,0,4]] a b, by
    have H : ∀ (a b : Fin 5), rowTable #v[#v[0,1,2,3,4],#v[0,1,0,0,0],#v[0,0,2,0,0],#v[0,0,0,3,0],#v[0,0,0,0,4]] a b < 5 := by decide +kernel
    exact H a b⟩
  symm := by decide +kernel
  noloop := by decide +kernel
  zero := by decide +kernel
  triangle := by decide +kernel
  edgeBound := by decide +kernel
  nextOK := by decide +kernel

theorem low_attains_12 : VertexAttains 12 := by
  apply model12.attains 1 2 3 4
  · constructor <;> decide
  · decide +kernel
  · decide


def model13 : SmallGraphData 5 where
  edge := boolEdge #v[2,5,10,20,8]
  dist := rowTable #v[#v[0,1,2,3,4],#v[1,0,1,2,3],#v[2,1,0,1,2],#v[3,2,1,0,1],#v[4,3,2,1,0]]
  next := fun a b => ⟨rowTable #v[#v[0,1,1,1,1],#v[0,1,2,2,2],#v[1,1,2,3,3],#v[2,2,2,3,4],#v[3,3,3,3,4]] a b, by
    have H : ∀ (a b : Fin 5), rowTable #v[#v[0,1,1,1,1],#v[0,1,2,2,2],#v[1,1,2,3,3],#v[2,2,2,3,4],#v[3,3,3,3,4]] a b < 5 := by decide +kernel
    exact H a b⟩
  symm := by decide +kernel
  noloop := by decide +kernel
  zero := by decide +kernel
  triangle := by decide +kernel
  edgeBound := by decide +kernel
  nextOK := by decide +kernel

theorem low_attains_13 : VertexAttains 13 := by
  apply model13.attains 0 1 2 4
  · constructor <;> decide
  · decide +kernel
  · decide


def model14 : SmallGraphData 5 where
  edge := boolEdge #v[2,5,10,20,8]
  dist := rowTable #v[#v[0,1,2,3,4],#v[1,0,1,2,3],#v[2,1,0,1,2],#v[3,2,1,0,1],#v[4,3,2,1,0]]
  next := fun a b => ⟨rowTable #v[#v[0,1,1,1,1],#v[0,1,2,2,2],#v[1,1,2,3,3],#v[2,2,2,3,4],#v[3,3,3,3,4]] a b, by
    have H : ∀ (a b : Fin 5), rowTable #v[#v[0,1,1,1,1],#v[0,1,2,2,2],#v[1,1,2,3,3],#v[2,2,2,3,4],#v[3,3,3,3,4]] a b < 5 := by decide +kernel
    exact H a b⟩
  symm := by decide +kernel
  noloop := by decide +kernel
  zero := by decide +kernel
  triangle := by decide +kernel
  edgeBound := by decide +kernel
  nextOK := by decide +kernel

theorem low_attains_14 : VertexAttains 14 := by
  apply model14.attains 0 1 3 4
  · constructor <;> decide
  · decide +kernel
  · decide


def model15 : SmallGraphData 6 where
  edge := boolEdge #v[30,1,1,1,33,16]
  dist := rowTable #v[#v[0,1,1,1,1,2],#v[1,0,2,2,2,3],#v[1,2,0,2,2,3],#v[1,2,2,0,2,3],#v[1,2,2,2,0,1],#v[2,3,3,3,1,0]]
  next := fun a b => ⟨rowTable #v[#v[0,1,2,3,4,4],#v[0,1,0,0,0,0],#v[0,0,2,0,0,0],#v[0,0,0,3,0,0],#v[0,0,0,0,4,5],#v[4,4,4,4,4,5]] a b, by
    have H : ∀ (a b : Fin 6), rowTable #v[#v[0,1,2,3,4,4],#v[0,1,0,0,0,0],#v[0,0,2,0,0,0],#v[0,0,0,3,0,0],#v[0,0,0,0,4,5],#v[4,4,4,4,4,5]] a b < 6 := by decide +kernel
    exact H a b⟩
  symm := by decide +kernel
  noloop := by decide +kernel
  zero := by decide +kernel
  triangle := by decide +kernel
  edgeBound := by decide +kernel
  nextOK := by decide +kernel

theorem low_attains_15 : VertexAttains 15 := by
  apply model15.attains 1 2 3 5
  · constructor <;> decide
  · decide +kernel
  · decide

end HakKozerenkoSeparatorGraph
