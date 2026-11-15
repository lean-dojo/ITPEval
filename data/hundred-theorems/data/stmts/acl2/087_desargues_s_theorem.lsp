;; Statement-only formalization of Hundred Theorems artifact 087,
;; "Desargues's Theorem": in a projective plane over an arbitrary
;; commutative field, corresponding intersections of two perspective
;; triangles are collinear.  Points use nonzero homogeneous coordinates.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

(defstub ht087-carrier (x) t)
(defstub ht087-add-op (x y) t)
(defstub ht087-multiply-op (x y) t)
(defstub ht087-negate-op (x) t)
(defstub ht087-inverse-op (x) t)

(defun ht087-member-p (x)
  (if (ht087-carrier x) t nil))

(defun ht087-add (x y)
  (ht087-add-op x y))

(defun ht087-mul (x y)
  (ht087-multiply-op x y))

(defun ht087-neg (x)
  (ht087-negate-op x))

(defun ht087-inv (x)
  (ht087-inverse-op x))

(defun ht087-sub (x y)
  (ht087-add x (ht087-neg y)))

(defun-sk ht087-field-laws-p (zero one)
  (forall (x y z)
    (implies
     (and
      (ht087-member-p x)
      (ht087-member-p y)
      (ht087-member-p z))
     (and
      (ht087-member-p (ht087-add x y))
      (ht087-member-p (ht087-mul x y))
      (ht087-member-p (ht087-neg x))
      (ht087-member-p (ht087-inv x))
      (equal (ht087-add (ht087-add x y) z)
             (ht087-add x (ht087-add y z)))
      (equal (ht087-add x y) (ht087-add y x))
      (equal (ht087-add x zero) x)
      (equal (ht087-add x (ht087-neg x)) zero)
      (equal (ht087-mul (ht087-mul x y) z)
             (ht087-mul x (ht087-mul y z)))
      (equal (ht087-mul x y) (ht087-mul y x))
      (equal (ht087-mul x one) x)
      (equal (ht087-inv zero) zero)
      (implies
       (not (equal x zero))
       (equal (ht087-mul x (ht087-inv x)) one))
      (equal
       (ht087-mul x (ht087-add y z))
       (ht087-add (ht087-mul x y)
                  (ht087-mul x z)))))))

(defun ht087-field-p (zero one)
  (and
   (ht087-member-p zero)
   (ht087-member-p one)
   (not (equal zero one))
   (ht087-field-laws-p zero one)))

(defun ht087-point-p (zero point)
  (and
   (true-listp point)
   (equal (len point) 3)
   (ht087-member-p (nth 0 point))
   (ht087-member-p (nth 1 point))
   (ht087-member-p (nth 2 point))
   (or
    (not (equal (nth 0 point) zero))
    (not (equal (nth 1 point) zero))
    (not (equal (nth 2 point) zero)))))

(defun ht087-all-points-p (zero points)
  (if (consp points)
      (and
       (ht087-point-p zero (car points))
       (ht087-all-points-p zero (cdr points)))
    (equal points nil)))

(defun ht087-determinant (p q r)
  (ht087-add
   (ht087-sub
    (ht087-mul
     (nth 0 p)
     (ht087-sub
      (ht087-mul (nth 1 q) (nth 2 r))
      (ht087-mul (nth 2 q) (nth 1 r))))
    (ht087-mul
     (nth 1 p)
     (ht087-sub
      (ht087-mul (nth 0 q) (nth 2 r))
      (ht087-mul (nth 2 q) (nth 0 r)))))
   (ht087-mul
    (nth 2 p)
    (ht087-sub
     (ht087-mul (nth 0 q) (nth 1 r))
     (ht087-mul (nth 1 q) (nth 0 r))))))

(defun ht087-collinear-p (zero p q r)
  (equal (ht087-determinant p q r) zero))

(defun hundred-theorems-087-desargues-statement
    (zero one a a1 b b1 c c1 p q r s)
  (implies
   (and
    (ht087-field-p zero one)
    (ht087-all-points-p
     zero (list a a1 b b1 c c1 p q r s))
    (not (ht087-collinear-p zero a1 b s))
    (not (ht087-collinear-p zero a p c))
    (not (ht087-collinear-p zero a p r))
    (not (ht087-collinear-p zero a c b))
    (not (ht087-collinear-p zero a b r))
    (not (ht087-collinear-p zero c1 p a1))
    (not (ht087-collinear-p zero c1 p b))
    (not (ht087-collinear-p zero c1 p b1))
    (not (ht087-collinear-p zero c1 a1 s))
    (not (ht087-collinear-p zero c1 a1 b1))
    (not (ht087-collinear-p zero p c a1))
    (not (ht087-collinear-p zero p c b))
    (not (ht087-collinear-p zero p a1 r))
    (not (ht087-collinear-p zero p b q))
    (not (ht087-collinear-p zero p q b1))
    (not (ht087-collinear-p zero c b s))
    (not (ht087-collinear-p zero a1 q b1))
    (ht087-collinear-p zero p a1 a)
    (ht087-collinear-p zero p b b1)
    (ht087-collinear-p zero p c1 c)
    (ht087-collinear-p zero b c q)
    (ht087-collinear-p zero b1 c1 q)
    (ht087-collinear-p zero a r c)
    (ht087-collinear-p zero a1 c1 r)
    (ht087-collinear-p zero b s a)
    (ht087-collinear-p zero a1 s b1))
   (ht087-collinear-p zero q s r)))

(value-triple :itpeval-statement-checked)
:q
