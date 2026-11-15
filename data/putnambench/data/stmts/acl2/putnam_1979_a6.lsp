;; Statement-only formalization of PutnamBench artifact putnam_1979_a6:
;; for n real points p_0,...,p_(n-1) in [0,1], there is a distinct x in
;; [0,1] satisfying the stated reciprocal-distance harmonic bound. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Only the first n values of the source function occur in the theorem, so an
;; n-element ACL2 list represents them exactly. Conservative generic symbols
;; are ACL2's native presentation of the real scalar operations; no APPLY$
;; function universe or powerset-completeness surrogate is needed.
(defstub p79a6-scalar-p (x) t)
(defstub p79a6-add-op (x y) t)
(defstub p79a6-multiply-op (x y) t)
(defstub p79a6-negate-op (x) t)
(defstub p79a6-inverse-op (x) t)
(defstub p79a6-less-op (x y) t)

(defun p79a6-add (x y)
  (p79a6-add-op x y))

(defun p79a6-mul (x y)
  (p79a6-multiply-op x y))

(defun p79a6-neg (x)
  (p79a6-negate-op x))

(defun p79a6-inv (x)
  (p79a6-inverse-op x))

(defun p79a6-sub (x y)
  (p79a6-add x (p79a6-neg y)))

(defun p79a6-less (x y)
  (if (p79a6-less-op x y) t nil))

(defun p79a6-less-equal (x y)
  (not (p79a6-less y x)))

(defun p79a6-abs (x zero)
  (if (p79a6-less x zero)
      (p79a6-neg x)
    x))

(defun-sk p79a6-field-laws-p (zero one)
  (forall (x y z)
    (implies
     (and
      (p79a6-scalar-p x)
      (p79a6-scalar-p y)
      (p79a6-scalar-p z))
     (and
      (p79a6-scalar-p (p79a6-add x y))
      (p79a6-scalar-p (p79a6-mul x y))
      (p79a6-scalar-p (p79a6-neg x))
      (implies
       (not (equal x zero))
       (p79a6-scalar-p (p79a6-inv x)))
      (equal (p79a6-add (p79a6-add x y) z)
             (p79a6-add x (p79a6-add y z)))
      (equal (p79a6-add x y)
             (p79a6-add y x))
      (equal (p79a6-add x zero) x)
      (equal (p79a6-add x (p79a6-neg x)) zero)
      (equal (p79a6-mul (p79a6-mul x y) z)
             (p79a6-mul x (p79a6-mul y z)))
      (equal (p79a6-mul x y)
             (p79a6-mul y x))
      (equal (p79a6-mul x one) x)
      (implies
       (not (equal x zero))
       (equal (p79a6-mul x (p79a6-inv x)) one))
      (equal
       (p79a6-mul x (p79a6-add y z))
       (p79a6-add (p79a6-mul x y)
                  (p79a6-mul x z)))))))

(defun-sk p79a6-order-laws-p (zero)
  (forall (x y z)
    (implies
     (and
      (p79a6-scalar-p x)
      (p79a6-scalar-p y)
      (p79a6-scalar-p z))
     (and
      (not (p79a6-less x x))
      (or
       (equal x y)
       (p79a6-less x y)
       (p79a6-less y x))
      (implies
       (and
        (p79a6-less x y)
        (p79a6-less y z))
       (p79a6-less x z))
      (implies
       (p79a6-less x y)
       (p79a6-less
        (p79a6-add x z)
        (p79a6-add y z)))
      (implies
       (and
        (p79a6-less zero x)
        (p79a6-less zero y))
       (p79a6-less zero (p79a6-mul x y)))))))

(defun p79a6-ordered-field-p (zero one)
  (and
   (p79a6-scalar-p zero)
   (p79a6-scalar-p one)
   (not (equal zero one))
   (p79a6-less zero one)
   (p79a6-field-laws-p zero one)
   (p79a6-order-laws-p zero)))

(defun p79a6-point-list-p (points zero one)
  (if (consp points)
      (and
       (p79a6-scalar-p (car points))
       (p79a6-less-equal zero (car points))
       (p79a6-less-equal (car points) one)
       (p79a6-point-list-p (cdr points) zero one))
    (equal points nil)))

(defun p79a6-nat-value (n zero one)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      zero
    (p79a6-add
     (p79a6-nat-value (1- n) zero one)
     one)))

(defun p79a6-distinct-from-points-p (x points)
  (if (consp points)
      (and
       (not (equal x (car points)))
       (p79a6-distinct-from-points-p x (cdr points)))
    t))

(defun p79a6-reciprocal-distance-sum (x points zero)
  (if (consp points)
      (p79a6-add
       (p79a6-inv
        (p79a6-abs
         (p79a6-sub x (car points))
         zero))
       (p79a6-reciprocal-distance-sum x (cdr points) zero))
    zero))

(defun p79a6-harmonic-sum (count zero one)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      zero
    (let* ((i (1- count))
           (denominator (+ (* 2 i) 1)))
      (p79a6-add
       (p79a6-harmonic-sum i zero one)
       (p79a6-inv
        (p79a6-nat-value denominator zero one))))))

(defun p79a6-bound (n zero one)
  (p79a6-mul
   (p79a6-mul
    (p79a6-nat-value 8 zero one)
    (p79a6-nat-value n zero one))
   (p79a6-harmonic-sum n zero one)))

(defun p79a6-witness-p (x points n zero one)
  (and
   (p79a6-scalar-p x)
   (p79a6-less-equal zero x)
   (p79a6-less-equal x one)
   (p79a6-distinct-from-points-p x points)
   (p79a6-less-equal
    (p79a6-reciprocal-distance-sum x points zero)
    (p79a6-bound n zero one))))

(defun-sk p79a6-witness-exists-p (points n zero one)
  (exists (x)
    (p79a6-witness-p x points n zero one)))

;; Completeness is not needed for this finite theorem. For n>0, take the
;; 2*n+1 equally spaced grid points j/(2*n) and discard one nearest grid point
;; for each input point. At least n+1 grid points remain. For a fixed input
;; point, the two grid points at each successive distance contribute at most
;; 8*n/(2*i+1); summing over the inputs and averaging over the remaining grid
;; points gives the displayed bound. This construction uses only finite
;; ordered-field arithmetic, so quantifying over ordered fields does not
;; strengthen the source proposition.
(defun putnambench-putnam-1979-a6-statement
    (points n zero one)
  (implies
   (and
    (natp n)
    (true-listp points)
    (equal (len points) n)
    (p79a6-ordered-field-p zero one)
    (p79a6-point-list-p points zero one))
   (p79a6-witness-exists-p points n zero one)))

(value-triple :itpeval-statement-checked)
:q
