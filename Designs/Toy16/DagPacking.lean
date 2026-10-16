import Designs.Toy16.DagHardware
set_option linter.unusedSimpArgs false
namespace HDLean.Toy16.DagPhysical

theorem packOutputs_related {α β : Type} (R : α → β → Prop)
    (active : α) (pc : Vector α 8) (fetched : Vector α 16)
    (nextPc : Vector α 8) (writeEnable : α) (rd : Vector α 3) (result : Vector α 16)
    (storeEnable : α) (ea : Vector α 8) (storeData : Vector α 16) (trap : α)
    (active' : β) (pc' : Vector β 8) (fetched' : Vector β 16)
    (nextPc' : Vector β 8) (writeEnable' : β) (rd' : Vector β 3) (result' : Vector β 16)
    (storeEnable' : β) (ea' : Vector β 8) (storeData' : Vector β 16) (trap' : β)
    (ha : R active active') (hp : ∀ k : Fin 8, R pc[k] pc'[k])
    (hf : ∀ k : Fin 16, R fetched[k] fetched'[k]) (hn : ∀ k : Fin 8, R nextPc[k] nextPc'[k])
    (hw : R writeEnable writeEnable') (hr : ∀ k : Fin 3, R rd[k] rd'[k])
    (hv : ∀ k : Fin 16, R result[k] result'[k]) (hs : R storeEnable storeEnable')
    (he : ∀ k : Fin 8, R ea[k] ea'[k]) (hd : ∀ k : Fin 16, R storeData[k] storeData'[k])
    (ht : R trap trap') (k : Fin 79) :
    R (packOutputs active pc fetched nextPc writeEnable rd result storeEnable ea storeData trap)[k]
      (packOutputs active' pc' fetched' nextPc' writeEnable' rd' result' storeEnable' ea' storeData' trap')[k] := by
  simp only [packOutputs,Fin.getElem_fin,Vector.getElem_ofFn]
  by_cases h0 : k.val = 0
  · simp only [h0,↓reduceDIte,↓reduceIte]
    exact ha
  · by_cases h9 : k.val < 9
    · simp only [h0,h9,↓reduceDIte,↓reduceIte]
      exact hp ⟨k.val-1,by omega⟩
    · by_cases h25 : k.val < 25
      · simp only [h0,h9,h25,↓reduceDIte,↓reduceIte]
        exact hf ⟨k.val-9,by omega⟩
      · by_cases h33 : k.val < 33
        · simp only [h0,h9,h25,h33,↓reduceDIte,↓reduceIte]
          exact hn ⟨k.val-25,by omega⟩
        · by_cases he33 : k.val = 33
          · simp only [h0,h9,h25,h33,he33,↓reduceDIte,↓reduceIte]
            exact hw
          · by_cases h37 : k.val < 37
            · simp only [h0,h9,h25,h33,he33,h37,↓reduceDIte,↓reduceIte]
              exact hr ⟨k.val-34,by omega⟩
            · by_cases h53 : k.val < 53
              · simp only [h0,h9,h25,h33,he33,h37,h53,↓reduceDIte,↓reduceIte]
                exact hv ⟨k.val-37,by omega⟩
              · by_cases he53 : k.val = 53
                · simp only [h0,h9,h25,h33,he33,h37,h53,he53,↓reduceDIte,↓reduceIte]
                  exact hs
                · by_cases h62 : k.val < 62
                  · simp only [h0,h9,h25,h33,he33,h37,h53,he53,h62,↓reduceDIte,↓reduceIte]
                    exact he ⟨k.val-54,by omega⟩
                  · by_cases h78 : k.val < 78
                    · simp only [h0,h9,h25,h33,he33,h37,h53,he53,h62,h78,↓reduceDIte,↓reduceIte]
                      exact hd ⟨k.val-62,by omega⟩
                    · simpa only [h0,h9,h25,h33,he33,h37,h53,he53,h62,h78,↓reduceDIte,↓reduceIte] using ht


theorem outputBits_pack : Physical.outputBits =
    packOutputs Physical.active Physical.pc Physical.fetched Physical.nextPc Physical.writeEnable
      Physical.rd Physical.result (Physical.isOp 8) Physical.ea Physical.storeData Physical.trap := by
  unfold Physical.outputBits packOutputs
  apply congrArg Vector.ofFn
  funext k
  rfl

end HDLean.Toy16.DagPhysical
