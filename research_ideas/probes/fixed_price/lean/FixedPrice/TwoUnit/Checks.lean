import FixedPrice.TwoUnit.Model
import FixedPrice.TwoUnit.GeneralInstanceData
import FixedPrice.TwoUnit.SymmetricInstanceData

/-! Kernel evaluations for Theorem D (`decide +kernel`, exact natural-number arithmetic). -/

namespace FixedPrice.TwoUnit

theorem general_weights : weightsSum generalBuyers = generalProbDen ∧
    weightsSum generalSellers = generalProbDen := by
  constructor <;> decide +kernel

theorem general_ordered : buyersOrdered generalBuyers = true ∧
    sellersOrdered generalSellers = true := by
  constructor <;> decide +kernel

theorem general_mean : meanN generalSellers = 1290478121440886509470190711 := by
  decide +kernel

theorem general_opt : optN generalBuyers generalSellers =
    4513189719726172494926641252006617932851157 := by
  decide +kernel

theorem general_check : checkN generalBuyers generalSellers generalProbDen
    1290478121440886509470190711 4513189719726172494926641252006617932851157
    7290804 10000000 = true := by
  decide +kernel

theorem general_events_ne : eventsN generalBuyers generalSellers ≠ [] := by
  decide +kernel

theorem symmetric_reversed :
    symmetricBuyers = symmetricSellers.map fun p => ((p.1.2, p.1.1), p.2) := by
  decide +kernel

theorem symmetric_weights : weightsSum symmetricBuyers = symmetricProbDen ∧
    weightsSum symmetricSellers = symmetricProbDen := by
  constructor <;> decide +kernel

theorem symmetric_ordered : buyersOrdered symmetricBuyers = true ∧
    sellersOrdered symmetricSellers = true := by
  constructor <;> decide +kernel

theorem symmetric_mean : meanN symmetricSellers = 2790530813884550000000 := by
  decide +kernel

theorem symmetric_opt : optN symmetricBuyers symmetricSellers =
    4900000120872789526983168200000000 := by
  decide +kernel

theorem symmetric_check : checkN symmetricBuyers symmetricSellers symmetricProbDen
    2790530813884550000000 4900000120872789526983168200000000 83693 100000 = true := by
  decide +kernel

theorem symmetric_events_ne : eventsN symmetricBuyers symmetricSellers ≠ [] := by
  decide +kernel

end FixedPrice.TwoUnit
