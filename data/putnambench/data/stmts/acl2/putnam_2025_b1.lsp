;; Statement-only formalization of PutnamBench artifact putnam_2025_b1:
;; a two-coloring of the plane that assigns every noncollinear monochromatic
;; triangle's circumcenter the same color is constant. This file contains no
;; proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Circumcenters are rational expressions in the six point coordinates.
;; Conservative generic symbols therefore give ACL2 the exact first-order
;; theorem schema over the real field, without restricting the coloring to an
;; APPLY$ function object or introducing any axiom event.
(defstub p2025b1-scalar-p (x) t)
(defstub p2025b1-add-op (x y) t)
(defstub p2025b1-multiply-op (x y) t)
(defstub p2025b1-negate-op (x) t)
(defstub p2025b1-inverse-op (x) t)
(defstub p2025b1-color (x y) t)

(defun p2025b1-add (x y)
  (p2025b1-add-op x y))

(defun p2025b1-mul (x y)
  (p2025b1-multiply-op x y))

(defun p2025b1-neg (x)
  (p2025b1-negate-op x))

(defun p2025b1-inv (x)
  (p2025b1-inverse-op x))

(defun p2025b1-sub (x y)
  (p2025b1-add x (p2025b1-neg y)))

(defun p2025b1-square (x)
  (p2025b1-mul x x))

(defun p2025b1-two (one)
  (p2025b1-add one one))

(defun p2025b1-nat-value (n zero one)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      zero
    (p2025b1-add
     (p2025b1-nat-value (1- n) zero one)
     one)))

(defun-sk p2025b1-field-laws-p (zero one)
  (forall (x y z)
    (implies
     (and
      (p2025b1-scalar-p x)
      (p2025b1-scalar-p y)
      (p2025b1-scalar-p z))
     (and
      (p2025b1-scalar-p (p2025b1-add x y))
      (p2025b1-scalar-p (p2025b1-mul x y))
      (p2025b1-scalar-p (p2025b1-neg x))
      (implies
       (not (equal x zero))
       (p2025b1-scalar-p (p2025b1-inv x)))
      (equal (p2025b1-add (p2025b1-add x y) z)
             (p2025b1-add x (p2025b1-add y z)))
      (equal (p2025b1-add x y)
             (p2025b1-add y x))
      (equal (p2025b1-add x zero) x)
      (equal (p2025b1-add x (p2025b1-neg x)) zero)
      (equal (p2025b1-mul (p2025b1-mul x y) z)
             (p2025b1-mul x (p2025b1-mul y z)))
      (equal (p2025b1-mul x y)
             (p2025b1-mul y x))
      (equal (p2025b1-mul x one) x)
      (implies
       (not (equal x zero))
       (equal (p2025b1-mul x (p2025b1-inv x)) one))
      (equal
       (p2025b1-mul x (p2025b1-add y z))
       (p2025b1-add (p2025b1-mul x y)
                    (p2025b1-mul x z)))))))

(defun-sk p2025b1-characteristic-zero-p (zero one)
  (forall (n)
    (implies
     (and (natp n) (< 0 n))
     (not
      (equal
       (p2025b1-nat-value n zero one)
       zero)))))

(defun p2025b1-field-p (zero one)
  (and
   (p2025b1-scalar-p zero)
   (p2025b1-scalar-p one)
   (not (equal zero one))
   (p2025b1-field-laws-p zero one)
   (p2025b1-characteristic-zero-p zero one)))

(defun p2025b1-boolean-p (value)
  (or (equal value nil)
      (equal value t)))

(defun-sk p2025b1-coloring-p ()
  (forall (x y)
    (implies
     (and
      (p2025b1-scalar-p x)
      (p2025b1-scalar-p y))
     (p2025b1-boolean-p
      (p2025b1-color x y)))))

(defun p2025b1-determinant
    (ax ay bx by cx cy one)
  (p2025b1-mul
   (p2025b1-two one)
   (p2025b1-add
    (p2025b1-mul ax (p2025b1-sub by cy))
    (p2025b1-add
     (p2025b1-mul bx (p2025b1-sub cy ay))
     (p2025b1-mul cx (p2025b1-sub ay by))))))

(defun p2025b1-radius-square-term (x y)
  (p2025b1-add
   (p2025b1-square x)
   (p2025b1-square y)))

(defun p2025b1-center-x-numerator
    (ax ay bx by cx cy)
  (p2025b1-add
   (p2025b1-mul
    (p2025b1-radius-square-term ax ay)
    (p2025b1-sub by cy))
   (p2025b1-add
    (p2025b1-mul
     (p2025b1-radius-square-term bx by)
     (p2025b1-sub cy ay))
    (p2025b1-mul
     (p2025b1-radius-square-term cx cy)
     (p2025b1-sub ay by)))))

(defun p2025b1-center-y-numerator
    (ax ay bx by cx cy)
  (p2025b1-add
   (p2025b1-mul
    (p2025b1-radius-square-term ax ay)
    (p2025b1-sub cx bx))
   (p2025b1-add
    (p2025b1-mul
     (p2025b1-radius-square-term bx by)
     (p2025b1-sub ax cx))
    (p2025b1-mul
     (p2025b1-radius-square-term cx cy)
     (p2025b1-sub bx ax)))))

(defun p2025b1-center-x
    (ax ay bx by cx cy one)
  (p2025b1-mul
   (p2025b1-center-x-numerator ax ay bx by cx cy)
   (p2025b1-inv
    (p2025b1-determinant ax ay bx by cx cy one))))

(defun p2025b1-center-y
    (ax ay bx by cx cy one)
  (p2025b1-mul
   (p2025b1-center-y-numerator ax ay bx by cx cy)
   (p2025b1-inv
    (p2025b1-determinant ax ay bx by cx cy one))))

(defun p2025b1-same-color-p
    (ax ay bx by cx cy)
  (and
   (equal (p2025b1-color ax ay)
          (p2025b1-color bx by))
   (equal (p2025b1-color ax ay)
          (p2025b1-color cx cy))))

(defun-sk p2025b1-circumcenter-closure-p (zero one)
  (forall (ax ay bx by cx cy)
    (implies
     (and
      (p2025b1-scalar-p ax)
      (p2025b1-scalar-p ay)
      (p2025b1-scalar-p bx)
      (p2025b1-scalar-p by)
      (p2025b1-scalar-p cx)
      (p2025b1-scalar-p cy)
      (not
       (equal
        (p2025b1-determinant ax ay bx by cx cy one)
        zero))
      (p2025b1-same-color-p ax ay bx by cx cy))
     (equal
      (p2025b1-color
       (p2025b1-center-x ax ay bx by cx cy one)
       (p2025b1-center-y ax ay bx by cx cy one))
      (p2025b1-color ax ay)))))

(defun-sk p2025b1-all-color-p (color-value)
  (forall (x y)
    (implies
     (and
      (p2025b1-scalar-p x)
      (p2025b1-scalar-p y))
     (equal
      (p2025b1-color x y)
      color-value))))

(defun p2025b1-monochromatic-p ()
  (or
   (p2025b1-all-color-p nil)
   (p2025b1-all-color-p t)))

(defun putnambench-putnam-2025-b1-statement
    (zero one)
  (implies
   (and
    (p2025b1-field-p zero one)
    (p2025b1-coloring-p)
    (p2025b1-circumcenter-closure-p zero one))
   (p2025b1-monochromatic-p)))

(value-triple :itpeval-statement-checked)
:q
