;; Statement-only formalization of PutnamBench corpus artifact putnam_1967_a5:
;; every convex region in the real Euclidean plane with area greater than
;; pi/4 contains two points exactly one unit apart. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The following conservative symbols present the scalar field and one
;; arbitrary plane region. Every field, order, square-root, Archimedean, and
;; pi requirement used below is explicit in the statement predicate.
(defstub p67a5-scalar-p (x) t)
(defstub p67a5-add-op (x y) t)
(defstub p67a5-mul-op (x y) t)
(defstub p67a5-neg-op (x) t)
(defstub p67a5-inv-op (x) t)
(defstub p67a5-lt-op (x y) t)
(defstub p67a5-region-member-op (x y) t)

(defun p67a5-add (x y)
  (p67a5-add-op x y))

(defun p67a5-mul (x y)
  (p67a5-mul-op x y))

(defun p67a5-neg (x)
  (p67a5-neg-op x))

(defun p67a5-inv (x)
  (p67a5-inv-op x))

(defun p67a5-sub (x y)
  (p67a5-add x (p67a5-neg y)))

(defun p67a5-lt-p (x y)
  (if (p67a5-lt-op x y) t nil))

(defun p67a5-le-p (x y)
  (not (p67a5-lt-p y x)))

(defun p67a5-region-member-p (x y)
  (if (p67a5-region-member-op x y) t nil))

(defun p67a5-nat-value (n zero one)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      zero
    (p67a5-add
     (p67a5-nat-value (1- n) zero one)
     one)))

(defun-sk p67a5-field-laws-p (zero one)
  (forall (x y z)
    (implies
     (and (p67a5-scalar-p x)
          (p67a5-scalar-p y)
          (p67a5-scalar-p z))
     (and
      (p67a5-scalar-p (p67a5-add x y))
      (p67a5-scalar-p (p67a5-mul x y))
      (p67a5-scalar-p (p67a5-neg x))
      (implies
       (not (equal x zero))
       (p67a5-scalar-p (p67a5-inv x)))
      (equal (p67a5-add (p67a5-add x y) z)
             (p67a5-add x (p67a5-add y z)))
      (equal (p67a5-add x y)
             (p67a5-add y x))
      (equal (p67a5-add x zero) x)
      (equal (p67a5-add x (p67a5-neg x)) zero)
      (equal (p67a5-mul (p67a5-mul x y) z)
             (p67a5-mul x (p67a5-mul y z)))
      (equal (p67a5-mul x y)
             (p67a5-mul y x))
      (equal (p67a5-mul x one) x)
      (implies
       (not (equal x zero))
       (equal (p67a5-mul x (p67a5-inv x)) one))
      (equal
       (p67a5-mul x (p67a5-add y z))
       (p67a5-add (p67a5-mul x y)
                  (p67a5-mul x z)))))))

(defun-sk p67a5-order-laws-p (zero)
  (forall (x y z)
    (implies
     (and (p67a5-scalar-p x)
          (p67a5-scalar-p y)
          (p67a5-scalar-p z))
     (and
      (not (p67a5-lt-p x x))
      (or (equal x y)
          (p67a5-lt-p x y)
          (p67a5-lt-p y x))
      (implies
       (and (p67a5-lt-p x y)
            (p67a5-lt-p y z))
       (p67a5-lt-p x z))
      (implies
       (p67a5-lt-p x y)
       (p67a5-lt-p
        (p67a5-add x z)
        (p67a5-add y z)))
      (implies
       (and (p67a5-lt-p zero x)
            (p67a5-lt-p zero y))
       (p67a5-lt-p zero (p67a5-mul x y)))))))

(defun-sk p67a5-archimedean-bound-exists-p
    (x zero one)
  (exists (n)
    (and (natp n)
         (p67a5-lt-p
          x
          (p67a5-nat-value n zero one)))))

(defun-sk p67a5-archimedean-p (zero one)
  (forall (x)
    (implies
     (p67a5-scalar-p x)
     (p67a5-archimedean-bound-exists-p
      x zero one))))

(defun-sk p67a5-nonnegative-square-root-exists-p
    (x zero)
  (exists (root)
    (and
     (p67a5-scalar-p root)
     (p67a5-le-p zero root)
     (equal (p67a5-mul root root) x))))

(defun-sk p67a5-square-root-closed-p (zero)
  (forall (x)
    (implies
     (and (p67a5-scalar-p x)
          (p67a5-le-p zero x))
     (p67a5-nonnegative-square-root-exists-p
      x zero))))

(defun p67a5-real-scalar-context-p (zero one)
  (and
   (p67a5-scalar-p zero)
   (p67a5-scalar-p one)
   (not (equal zero one))
   (p67a5-field-laws-p zero one)
   (p67a5-order-laws-p zero)
   (p67a5-lt-p zero one)
   (p67a5-archimedean-p zero one)
   (p67a5-square-root-closed-p zero)))

;; Paired Gregory-Leibniz sums give exact lower and upper bounds converging
;; to pi. PI is therefore an element of the presented real scalar field, not
;; a rational approximation or an externally supplied area witness.
(defun p67a5-leibniz-pair-sum
    (remaining index zero one)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      zero
    (p67a5-add
     (p67a5-add
      (p67a5-inv
       (p67a5-nat-value
        (+ (* 4 index) 1) zero one))
      (p67a5-neg
       (p67a5-inv
        (p67a5-nat-value
         (+ (* 4 index) 3) zero one))))
     (p67a5-leibniz-pair-sum
      (1- remaining) (1+ index) zero one))))

(defun p67a5-four (one)
  (p67a5-add
   (p67a5-add one one)
   (p67a5-add one one)))

(defun p67a5-pi-lower (n zero one)
  (p67a5-mul
   (p67a5-four one)
   (p67a5-leibniz-pair-sum
    (nfix n) 0 zero one)))

(defun p67a5-pi-upper (n zero one)
  (p67a5-add
   (p67a5-pi-lower n zero one)
   (p67a5-mul
    (p67a5-four one)
    (p67a5-inv
     (p67a5-nat-value
      (+ (* 4 (nfix n)) 1) zero one)))))

(defun-sk p67a5-pi-bounds-p (pi-value zero one)
  (forall (n)
    (implies
     (natp n)
     (and
      (p67a5-lt-p
       (p67a5-pi-lower n zero one)
       pi-value)
      (p67a5-lt-p
       pi-value
       (p67a5-pi-upper n zero one))))))

(defun p67a5-pi-p (pi-value zero one)
  (and
   (p67a5-scalar-p pi-value)
   (p67a5-pi-bounds-p pi-value zero one)))

(defun p67a5-point-p (point)
  (and
   (consp point)
   (p67a5-scalar-p (car point))
   (p67a5-scalar-p (cdr point))))

(defun p67a5-point-list-p (points)
  (if (consp points)
      (and
       (p67a5-point-p (car points))
       (p67a5-point-list-p (cdr points)))
    (equal points nil)))

(defun p67a5-distinct-point-list-p (points)
  (if (consp points)
      (and
       (not (member-equal (car points) (cdr points)))
       (p67a5-distinct-point-list-p (cdr points)))
    (equal points nil)))

(defun p67a5-oriented-area (a b c)
  (p67a5-sub
   (p67a5-mul
    (p67a5-sub (car b) (car a))
    (p67a5-sub (cdr c) (cdr a)))
   (p67a5-mul
    (p67a5-sub (cdr b) (cdr a))
    (p67a5-sub (car c) (car a)))))

(defun p67a5-all-left-of-edge-p
    (a b points zero)
  (if (consp points)
      (and
       (or
        (equal (car points) a)
        (equal (car points) b)
        (p67a5-lt-p
         zero
         (p67a5-oriented-area
          a b (car points))))
       (p67a5-all-left-of-edge-p
        a b (cdr points) zero))
    (equal points nil)))

(defun p67a5-convex-edges-aux-p
    (first current remaining all-points zero)
  (if (consp remaining)
      (and
       (p67a5-all-left-of-edge-p
        current (car remaining) all-points zero)
       (p67a5-convex-edges-aux-p
        first
        (car remaining)
        (cdr remaining)
        all-points
        zero))
    (p67a5-all-left-of-edge-p
     current first all-points zero)))

(defun p67a5-strictly-convex-polygon-p
    (points zero)
  (and
   (true-listp points)
   (<= 3 (len points))
   (p67a5-point-list-p points)
   (p67a5-distinct-point-list-p points)
   (p67a5-convex-edges-aux-p
    (car points)
    (car points)
    (cdr points)
    points
    zero)))

(defun p67a5-origin-cross (a b)
  (p67a5-sub
   (p67a5-mul (car a) (cdr b))
   (p67a5-mul (cdr a) (car b))))

(defun p67a5-double-area-aux
    (first current remaining)
  (if (consp remaining)
      (p67a5-add
       (p67a5-origin-cross
        current (car remaining))
       (p67a5-double-area-aux
        first
        (car remaining)
        (cdr remaining)))
    (p67a5-origin-cross current first)))

(defun p67a5-double-area (points zero)
  (if (consp points)
      (p67a5-double-area-aux
       (car points)
       (car points)
       (cdr points))
    zero))

(defun p67a5-points-in-region-p (points)
  (if (consp points)
      (and
       (p67a5-region-member-p
        (car (car points))
        (cdr (car points)))
       (p67a5-points-in-region-p
        (cdr points)))
    (equal points nil)))

;; For a convex plane region, Lebesgue area greater than pi/4 is equivalent
;; to containing a finite strictly convex real polygon whose area is still
;; greater than pi/4. The polygon is an internal witness for the source area
;; hypothesis; it is not the region and does not replace the source domain.
(defun-sk p67a5-large-inscribed-polygon-exists-p
    (pi-value zero one)
  (exists (points)
    (and
     (p67a5-strictly-convex-polygon-p
      points zero)
     (p67a5-points-in-region-p points)
     (p67a5-lt-p
      pi-value
      (p67a5-mul
       (p67a5-add one one)
       (p67a5-double-area points zero))))))

(defun-sk p67a5-region-convex-p (zero one)
  (forall (ax ay bx by weight)
    (implies
     (and
      (p67a5-scalar-p ax)
      (p67a5-scalar-p ay)
      (p67a5-scalar-p bx)
      (p67a5-scalar-p by)
      (p67a5-scalar-p weight)
      (p67a5-region-member-p ax ay)
      (p67a5-region-member-p bx by)
      (p67a5-le-p zero weight)
      (p67a5-le-p weight one))
     (p67a5-region-member-p
      (p67a5-add
       (p67a5-mul
        (p67a5-sub one weight) ax)
       (p67a5-mul weight bx))
      (p67a5-add
       (p67a5-mul
        (p67a5-sub one weight) ay)
       (p67a5-mul weight by))))))

(defun p67a5-distance-squared
    (px py qx qy)
  (p67a5-add
   (p67a5-mul
    (p67a5-sub px qx)
    (p67a5-sub px qx))
   (p67a5-mul
    (p67a5-sub py qy)
    (p67a5-sub py qy))))

(defun-sk p67a5-unit-distance-pair-exists-p (one)
  (exists (px py qx qy)
    (and
     (p67a5-scalar-p px)
     (p67a5-scalar-p py)
     (p67a5-scalar-p qx)
     (p67a5-scalar-p qy)
     (p67a5-region-member-p px py)
     (p67a5-region-member-p qx qy)
     (equal
      (p67a5-distance-squared
       px py qx qy)
      one))))

(defun putnambench-putnam-1967-a5-statement
    (zero one pi-value)
  (implies
   (and
    (p67a5-real-scalar-context-p zero one)
    (p67a5-pi-p pi-value zero one)
    (p67a5-region-convex-p zero one)
    (p67a5-large-inscribed-polygon-exists-p
     pi-value zero one))
   (p67a5-unit-distance-pair-exists-p one)))

(value-triple :itpeval-statement-checked)
:q
