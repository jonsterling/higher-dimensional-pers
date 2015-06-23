module terms where

mutual
  data val : Set where
    unit void : val
    <> : val
    ze : val
    su : exp → val
    idpath : val
    Paths : exp → exp → exp → val
    Interval I0 I1 seg : val

  data exp : Set where
    `_ : val → exp
    sympath : exp → exp
    _,_ : exp → exp → exp

