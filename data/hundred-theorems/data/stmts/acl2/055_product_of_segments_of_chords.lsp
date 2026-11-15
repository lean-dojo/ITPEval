;; Statement-only formalization of Hundred Theorems artifact 055, "Product
;; of Segments of Chords": two chords meeting inside a circle have equal
;; products of segment lengths.  Squared distances avoid introducing square
;; roots; over the real plane this is equivalent to the usual statement.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative generic symbols describe an arbitrary strict ordered
;; commutative ring.  The theorem uses only polynomial plane geometry.
(defstub ht055-carrier (x) t)
(defstub ht055-add-op (x y) t)
(defstub ht055-multiply-op (x y) t)
(defstub ht055-negate-op (x) t)
(defstub ht055-less-op (x y) t)

(defun ht055-member-p (x)
  (if (ht055-carrier x) t nil))

(defun ht055-add (x y)
  (ht055-add-op x y))

(defun ht055-mul (x y)
  (ht055-multiply-op x y))

(defun ht055-neg (x)
  (ht055-negate-op x))

(defun ht055-sub (x y)
  (ht055-add x (ht055-neg y)))

(defun ht055-less (x y)
  (if (ht055-less-op x y) t nil))

(defun ht055-leq (x y)
  (not (ht055-less y x)))

(defun-sk ht055-ring-laws-p (zero one)
  (forall (x y z)
    (implies
     (and
      (ht055-member-p x)
      (ht055-member-p y)
      (ht055-member-p z))
     (and
      (ht055-member-p (ht055-add x y))
      (ht055-member-p (ht055-mul x y))
      (ht055-member-p (ht055-neg x))
      (equal (ht055-add (ht055-add x y) z)
             (ht055-add x (ht055-add y z)))
      (equal (ht055-add x y) (ht055-add y x))
      (equal (ht055-add x zero) x)
      (equal (ht055-add x (ht055-neg x)) zero)
      (equal (ht055-mul (ht055-mul x y) z)
             (ht055-mul x (ht055-mul y z)))
      (equal (ht055-mul x y) (ht055-mul y x))
      (equal (ht055-mul x one) x)
      (equal
       (ht055-mul x (ht055-add y z))
       (ht055-add (ht055-mul x y)
                  (ht055-mul x z)))))))

(defun-sk ht055-order-laws-p (zero)
  (forall (x y z)
    (implies
     (and
      (ht055-member-p x)
      (ht055-member-p y)
      (ht055-member-p z))
     (and
      (not (ht055-less x x))
      (or (equal x y)
          (ht055-less x y)
          (ht055-less y x))
      (implies
       (and (ht055-less x y)
            (ht055-less y z))
       (ht055-less x z))
      (implies
       (ht055-less x y)
       (ht055-less (ht055-add x z)
                   (ht055-add y z)))
      (implies
       (and (ht055-less zero x)
            (ht055-less zero y))
       (ht055-less zero (ht055-mul x y)))))))

(defun ht055-ordered-ring-p (zero one)
  (and
   (ht055-member-p zero)
   (ht055-member-p one)
   (not (equal zero one))
   (ht055-less zero one)
   (ht055-ring-laws-p zero one)
   (ht055-order-laws-p zero)))

(defun ht055-point-p (point)
  (and
   (true-listp point)
   (equal (len point) 2)
   (ht055-member-p (nth 0 point))
   (ht055-member-p (nth 1 point))))

(defun ht055-all-points-p (points)
  (if (consp points)
      (and
       (ht055-point-p (car points))
       (ht055-all-points-p (cdr points)))
    (equal points nil)))

(defun ht055-square (x)
  (ht055-mul x x))

(defun ht055-squared-distance (p q)
  (ht055-add
   (ht055-square
    (ht055-sub (nth 0 p) (nth 0 q)))
   (ht055-square
    (ht055-sub (nth 1 p) (nth 1 q)))))

(defun ht055-collinear-p (p q r)
  (equal
   (ht055-mul
    (ht055-sub (nth 0 q) (nth 0 p))
    (ht055-sub (nth 1 r) (nth 1 p)))
   (ht055-mul
    (ht055-sub (nth 1 q) (nth 1 p))
    (ht055-sub (nth 0 r) (nth 0 p)))))

;; B lies between Q and R exactly when the two displacement vectors from B
;; have a nonpositive dot product.
(defun ht055-between-p (zero q b r)
  (ht055-leq
   (ht055-add
    (ht055-mul
     (ht055-sub (nth 0 q) (nth 0 b))
     (ht055-sub (nth 0 r) (nth 0 b)))
    (ht055-mul
     (ht055-sub (nth 1 q) (nth 1 b))
     (ht055-sub (nth 1 r) (nth 1 b))))
   zero))

(defun ht055-on-circle-p (centre radius point)
  (equal
   (ht055-squared-distance centre point)
   (ht055-square radius)))

(defun hundred-theorems-055-product-of-segments-of-chords-statement
    (zero one centre radius q r s t-point b)
  (implies
   (and
    (ht055-ordered-ring-p zero one)
    (ht055-member-p radius)
    (ht055-leq zero radius)
    (ht055-all-points-p
     (list centre q r s t-point b))
    (ht055-on-circle-p centre radius q)
    (ht055-on-circle-p centre radius r)
    (ht055-on-circle-p centre radius s)
    (ht055-on-circle-p centre radius t-point)
    (ht055-collinear-p q b r)
    (ht055-collinear-p s b t-point)
    (ht055-between-p zero q b r)
    (ht055-between-p zero s b t-point))
   (equal
    (ht055-mul
     (ht055-squared-distance b q)
     (ht055-squared-distance b r))
    (ht055-mul
     (ht055-squared-distance b s)
     (ht055-squared-distance b t-point)))))

(value-triple :itpeval-statement-checked)
:q
