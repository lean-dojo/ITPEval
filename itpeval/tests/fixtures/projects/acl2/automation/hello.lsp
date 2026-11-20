(in-package "ACL2")

(defthm itpeval-target
  (implies (and (equal (car xs) a) (equal (cons a tail) ys))
           (equal (car xs) (car ys)))
  :instructions (:promote :bash)
  :rule-classes nil)

:q
