(in-package "ACL2")

(defthm itpeval-target
  (equal (car (cons x y)) x)
  :hints nil
  :rule-classes nil)

(assert-event (getpropc 'itpeval-target 'theorem nil (w state)))
(value-triple :itpeval-target-admitted)
:q
