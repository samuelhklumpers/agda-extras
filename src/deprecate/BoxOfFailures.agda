module BoxOfFailures where


module Test (X : Set) (Y : X → Set) where
  record A (x : X) : Set where
    field
      a : Y x

  open A {{...}} public

  record B (x : X) : Set where
    field
      b : A x

  open B {{...}}

  record C : Set where
    field
      {{c}} : {x : X} → B x 
      
  open C {{...}} public

  instance
    z : {x : X} → {{B x}} → A x
    z = b

  d : {{C}} → (x : X) → Y x
  d x = a

  e : (x : X) → {{B x}} → Y x
  e x = a


module InstancesArentAlwaysTransitive where
  data I : Set where

  -- some basic class
  record F0 (F : Set → Set) : Set₁ where
    field 
      fmap : ∀ {A B} → (A → B) → F A → F B

  open F0 {{...}}

  -- add some information, or simply pass through the class directly
  record F1 (F : Set → Set) : Set₁ where
    field
      {{super}} : F0 F

  open F1 {{...}}

  -- indexed applicatives are nice 
  record A0 (F : I → I → Set → Set) : Set₁ where
    field
      --                 (*) v try changing this to F1
      {{super}} : ∀ {i j} → F0 (F i j)

  open A0 {{...}}

  -- similarly, add some information or pass through
  record A1 (F : I → I → Set → Set) : Set₁ where
    field
      {{super}} : A0 F

  open A1 {{...}}

  -- last one
  record M0 (F : I → I → Set → Set) : Set₁ where
    field
      {{super}} : A0 F

    -- let's use something from the bottom of the chain
    c : ∀ {i j A} → F i j A → F i j A 
    c x = fmap (λ y → y) x

    -- but what happens if we didn't skip F1 at (*)?

  record M0' (F : I → I → Set → Set) : Set₁ where
    field
      --           v yet this is unproblematic
      {{super}} : A1 F

    c : ∀ {i j A} → F i j A → F i j A 
    c x = fmap (λ y → y) x
