(in-package "ACL2")

(defthm itpeval-target
  (equal (car (cons x y)) x)
  :instructions (:s)
  :rule-classes nil)

:q
