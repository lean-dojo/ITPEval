;; Statement-only formalization of PutnamBench artifact putnam_1994_a3:
;; every four-coloring of the closed unit isosceles right triangle has two
;; same-colored points at distance at least 2 - sqrt(2). This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The theorem uses only ordered-field arithmetic, one positive square root
;; of two, and an arbitrary coloring. Conservative generic symbols are the
;; standard ACL2 presentation of those universally quantified objects; no
;; completeness axiom or restricted APPLY$ function universe is needed.
(defstub p1994a3-scalar-p (x) t)
(defstub p1994a3-add-op (x y) t)
(defstub p1994a3-multiply-op (x y) t)
(defstub p1994a3-negate-op (x) t)
(defstub p1994a3-inverse-op (x) t)
(defstub p1994a3-less-op (x y) t)
(defstub p1994a3-color (point) t)

(defun p1994a3-add (x y)
  (p1994a3-add-op x y))

(defun p1994a3-mul (x y)
  (p1994a3-multiply-op x y))

(defun p1994a3-neg (x)
  (p1994a3-negate-op x))

(defun p1994a3-inv (x)
  (p1994a3-inverse-op x))

(defun p1994a3-sub (x y)
  (p1994a3-add x (p1994a3-neg y)))

(defun p1994a3-less (x y)
  (if (p1994a3-less-op x y) t nil))

(defun p1994a3-less-equal (x y)
  (not (p1994a3-less y x)))

(defun p1994a3-square (x)
  (p1994a3-mul x x))

(defun-sk p1994a3-field-laws-p (zero one)
  (forall (x y z)
    (implies
     (and
      (p1994a3-scalar-p x)
      (p1994a3-scalar-p y)
      (p1994a3-scalar-p z))
     (and
      (p1994a3-scalar-p (p1994a3-add x y))
      (p1994a3-scalar-p (p1994a3-mul x y))
      (p1994a3-scalar-p (p1994a3-neg x))
      (implies
       (not (equal x zero))
       (p1994a3-scalar-p (p1994a3-inv x)))
      (equal (p1994a3-add (p1994a3-add x y) z)
             (p1994a3-add x (p1994a3-add y z)))
      (equal (p1994a3-add x y)
             (p1994a3-add y x))
      (equal (p1994a3-add x zero) x)
      (equal (p1994a3-add x (p1994a3-neg x)) zero)
      (equal (p1994a3-mul (p1994a3-mul x y) z)
             (p1994a3-mul x (p1994a3-mul y z)))
      (equal (p1994a3-mul x y)
             (p1994a3-mul y x))
      (equal (p1994a3-mul x one) x)
      (implies
       (not (equal x zero))
       (equal (p1994a3-mul x (p1994a3-inv x)) one))
      (equal
       (p1994a3-mul x (p1994a3-add y z))
       (p1994a3-add (p1994a3-mul x y)
                    (p1994a3-mul x z)))))))

(defun-sk p1994a3-order-laws-p (zero)
  (forall (x y z)
    (implies
     (and
      (p1994a3-scalar-p x)
      (p1994a3-scalar-p y)
      (p1994a3-scalar-p z))
     (and
      (not (p1994a3-less x x))
      (or
       (equal x y)
       (p1994a3-less x y)
       (p1994a3-less y x))
      (implies
       (and
        (p1994a3-less x y)
        (p1994a3-less y z))
       (p1994a3-less x z))
      (implies
       (p1994a3-less x y)
       (p1994a3-less
        (p1994a3-add x z)
        (p1994a3-add y z)))
      (implies
       (and
        (p1994a3-less zero x)
        (p1994a3-less zero y))
       (p1994a3-less zero (p1994a3-mul x y)))))))

(defun p1994a3-ordered-field-p (zero one)
  (and
   (p1994a3-scalar-p zero)
   (p1994a3-scalar-p one)
   (not (equal zero one))
   (p1994a3-less zero one)
   (p1994a3-field-laws-p zero one)
   (p1994a3-order-laws-p zero)))

(defun p1994a3-point-p (point)
  (and
   (true-listp point)
   (equal (len point) 2)
   (p1994a3-scalar-p (nth 0 point))
   (p1994a3-scalar-p (nth 1 point))))

(defun p1994a3-triangle-point-p (point zero one)
  (and
   (p1994a3-point-p point)
   (p1994a3-less-equal zero (nth 0 point))
   (p1994a3-less-equal zero (nth 1 point))
   (p1994a3-less-equal
    (p1994a3-add (nth 0 point) (nth 1 point))
    one)))

(defun p1994a3-color-p (color)
  (and (natp color) (< color 4)))

(defun-sk p1994a3-coloring-p (zero one)
  (forall (point)
    (implies
     (p1994a3-triangle-point-p point zero one)
     (p1994a3-color-p (p1994a3-color point)))))

(defun p1994a3-sqrt-two-p (sqrt-two zero one)
  (let ((two (p1994a3-add one one)))
    (and
     (p1994a3-scalar-p sqrt-two)
     (p1994a3-less zero sqrt-two)
     (p1994a3-less sqrt-two two)
     (equal (p1994a3-square sqrt-two) two))))

(defun p1994a3-distance-squared (left right)
  (let ((dx (p1994a3-sub (nth 0 left) (nth 0 right)))
        (dy (p1994a3-sub (nth 1 left) (nth 1 right))))
    (p1994a3-add
     (p1994a3-square dx)
     (p1994a3-square dy))))

(defun p1994a3-bound-squared (sqrt-two one)
  (let ((two (p1994a3-add one one)))
    (p1994a3-square (p1994a3-sub two sqrt-two))))

(defun-sk p1994a3-separated-pair-exists-p
    (sqrt-two zero one)
  (exists (left right)
    (and
     (p1994a3-triangle-point-p left zero one)
     (p1994a3-triangle-point-p right zero one)
     (equal (p1994a3-color left)
            (p1994a3-color right))
     (p1994a3-less-equal
      (p1994a3-bound-squared sqrt-two one)
      (p1994a3-distance-squared left right)))))

(defun putnambench-putnam-1994-a3-statement
    (sqrt-two zero one)
  (implies
   (and
    (p1994a3-ordered-field-p zero one)
    (p1994a3-sqrt-two-p sqrt-two zero one)
    (p1994a3-coloring-p zero one))
   (p1994a3-separated-pair-exists-p
    sqrt-two zero one)))

(value-triple :itpeval-statement-checked)
:q
