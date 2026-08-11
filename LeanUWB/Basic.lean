/-- Writing `↓t` is slightly more general than writing `Function.const _ t`. -/
notation:max "↓"t:arg => (fun _ => t)

/-- The left-to-right direction of `↔`. -/
postfix:max ".→" => Iff.mp

/-- The right-to-left direction of `↔`. -/
postfix:max ".←" => Iff.mpr
