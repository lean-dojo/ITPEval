(in-package "ACL2")

(defun plus-two-two ()
  (+ 2 2))

(defthm two-plus-two
  (equal (plus-two-two) 4)
  :rule-classes nil)

(value-triple :ok)
