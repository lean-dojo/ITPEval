;; Statement-only formalization of PutnamBench artifact putnam_2008_b3:
;; the largest radius of a circle contained in the side-one four-dimensional
;; hypercube is sqrt(2)/2. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The result is finite-dimensional ordered-field geometry. Conservative
;; generic symbols describe the scalar field and its nonnegative square-root
;; operation without restricting them to APPLY$ function objects.
(defstub p08b3-scalar-p (x) t)
(defstub p08b3-add-op (x y) t)
(defstub p08b3-multiply-op (x y) t)
(defstub p08b3-negate-op (x) t)
(defstub p08b3-inverse-op (x) t)
(defstub p08b3-less-op (x y) t)
(defstub p08b3-square-root-op (x) t)

(defun p08b3-add (x y)
  (p08b3-add-op x y))

(defun p08b3-mul (x y)
  (p08b3-multiply-op x y))

(defun p08b3-neg (x)
  (p08b3-negate-op x))

(defun p08b3-inv (x)
  (p08b3-inverse-op x))

(defun p08b3-less (x y)
  (if (p08b3-less-op x y) t nil))

(defun p08b3-sqrt (x)
  (p08b3-square-root-op x))

(defun p08b3-sub (x y)
  (p08b3-add x (p08b3-neg y)))

(defun p08b3-leq (x y)
  (not (p08b3-less y x)))

(defun p08b3-square (x)
  (p08b3-mul x x))

(defun p08b3-two (one)
  (p08b3-add one one))

(defun p08b3-half (one)
  (p08b3-inv (p08b3-two one)))

(defun-sk p08b3-field-laws-p (zero one)
  (forall (x y z)
    (implies
     (and
      (p08b3-scalar-p x)
      (p08b3-scalar-p y)
      (p08b3-scalar-p z))
     (and
      (p08b3-scalar-p (p08b3-add x y))
      (p08b3-scalar-p (p08b3-mul x y))
      (p08b3-scalar-p (p08b3-neg x))
      (implies
       (not (equal x zero))
       (p08b3-scalar-p (p08b3-inv x)))
      (equal (p08b3-add (p08b3-add x y) z)
             (p08b3-add x (p08b3-add y z)))
      (equal (p08b3-add x y)
             (p08b3-add y x))
      (equal (p08b3-add x zero) x)
      (equal (p08b3-add x (p08b3-neg x)) zero)
      (equal (p08b3-mul (p08b3-mul x y) z)
             (p08b3-mul x (p08b3-mul y z)))
      (equal (p08b3-mul x y)
             (p08b3-mul y x))
      (equal (p08b3-mul x one) x)
      (implies
       (not (equal x zero))
       (equal (p08b3-mul x (p08b3-inv x)) one))
      (equal
       (p08b3-mul x (p08b3-add y z))
       (p08b3-add (p08b3-mul x y)
                  (p08b3-mul x z)))))))

(defun-sk p08b3-order-laws-p (zero)
  (forall (x y z)
    (implies
     (and
      (p08b3-scalar-p x)
      (p08b3-scalar-p y)
      (p08b3-scalar-p z))
     (and
      (not (p08b3-less x x))
      (or
       (equal x y)
       (p08b3-less x y)
       (p08b3-less y x))
      (implies
       (and
        (p08b3-less x y)
        (p08b3-less y z))
       (p08b3-less x z))
      (implies
       (p08b3-less x y)
       (p08b3-less
        (p08b3-add x z)
        (p08b3-add y z)))
      (implies
       (and
        (p08b3-less zero x)
        (p08b3-less zero y))
       (p08b3-less zero (p08b3-mul x y)))))))

(defun-sk p08b3-square-root-laws-p (zero)
  (forall (x)
    (implies
     (p08b3-scalar-p x)
     (and
      (p08b3-scalar-p (p08b3-sqrt x))
      (implies
       (p08b3-leq zero x)
       (and
        (p08b3-leq zero (p08b3-sqrt x))
        (equal (p08b3-square (p08b3-sqrt x))
               x)))))))

(defun p08b3-scalar-context-p (zero one)
  (and
   (p08b3-scalar-p zero)
   (p08b3-scalar-p one)
   (not (equal zero one))
   (p08b3-less zero one)
   (p08b3-field-laws-p zero one)
   (p08b3-order-laws-p zero)
   (p08b3-square-root-laws-p zero)))

(defun p08b3-vector-p (vector)
  (and
   (true-listp vector)
   (equal (len vector) 4)
   (p08b3-scalar-p (nth 0 vector))
   (p08b3-scalar-p (nth 1 vector))
   (p08b3-scalar-p (nth 2 vector))
   (p08b3-scalar-p (nth 3 vector))))

(defun p08b3-zero-vector (zero)
  (list zero zero zero zero))

(defun p08b3-vector-add (left right)
  (list
   (p08b3-add (nth 0 left) (nth 0 right))
   (p08b3-add (nth 1 left) (nth 1 right))
   (p08b3-add (nth 2 left) (nth 2 right))
   (p08b3-add (nth 3 left) (nth 3 right))))

(defun p08b3-scalar-multiply (scalar vector)
  (list
   (p08b3-mul scalar (nth 0 vector))
   (p08b3-mul scalar (nth 1 vector))
   (p08b3-mul scalar (nth 2 vector))
   (p08b3-mul scalar (nth 3 vector))))

(defun p08b3-vector-norm-squared (vector)
  (p08b3-add
   (p08b3-square (nth 0 vector))
   (p08b3-add
    (p08b3-square (nth 1 vector))
    (p08b3-add
     (p08b3-square (nth 2 vector))
     (p08b3-square (nth 3 vector))))))

(defun p08b3-abs (x zero)
  (if (p08b3-less x zero)
      (p08b3-neg x)
    x))

(defun p08b3-hypercube-point-p (point zero one)
  (let ((half (p08b3-half one)))
    (and
     (p08b3-vector-p point)
     (p08b3-leq (p08b3-abs (nth 0 point) zero) half)
     (p08b3-leq (p08b3-abs (nth 1 point) zero) half)
     (p08b3-leq (p08b3-abs (nth 2 point) zero) half)
     (p08b3-leq (p08b3-abs (nth 3 point) zero) half))))

(defun p08b3-plane-displacement
    (alpha direction-p beta direction-q)
  (p08b3-vector-add
   (p08b3-scalar-multiply alpha direction-p)
   (p08b3-scalar-multiply beta direction-q)))

(defun-sk p08b3-linearly-independent-p
    (direction-p direction-q zero)
  (forall (alpha beta)
    (implies
     (and
      (p08b3-scalar-p alpha)
      (p08b3-scalar-p beta)
      (equal
       (p08b3-plane-displacement
        alpha direction-p beta direction-q)
       (p08b3-zero-vector zero)))
     (and
      (equal alpha zero)
      (equal beta zero)))))

;; A negative-radius sphere is empty. For a nonnegative radius, the squared
;; norm equation is exactly the circle in the represented affine plane.
(defun p08b3-on-circle-p
    (radius displacement zero)
  (and
   (p08b3-leq zero radius)
   (equal
    (p08b3-vector-norm-squared displacement)
    (p08b3-square radius))))

(defun-sk p08b3-circle-contained-p
    (radius center direction-p direction-q zero one)
  (forall (alpha beta)
    (implies
     (and
      (p08b3-scalar-p alpha)
      (p08b3-scalar-p beta)
      (p08b3-on-circle-p
       radius
       (p08b3-plane-displacement
        alpha direction-p beta direction-q)
       zero))
     (p08b3-hypercube-point-p
      (p08b3-vector-add
       center
       (p08b3-plane-displacement
        alpha direction-p beta direction-q))
      zero one))))

(defun-sk p08b3-contains-radius-p (radius zero one)
  (exists (center direction-p direction-q)
    (and
     (p08b3-scalar-p radius)
     (p08b3-vector-p center)
     (p08b3-vector-p direction-p)
     (p08b3-vector-p direction-q)
     (p08b3-linearly-independent-p
      direction-p direction-q zero)
     (p08b3-circle-contained-p
      radius center direction-p direction-q zero one))))

(defun-sk p08b3-is-upper-bound-p (radius zero one)
  (forall (other-radius)
    (implies
     (and
      (p08b3-scalar-p other-radius)
      (p08b3-contains-radius-p other-radius zero one))
     (p08b3-leq other-radius radius))))

(defun putnambench-putnam-2008-b3-statement
    (zero one)
  (implies
   (p08b3-scalar-context-p zero one)
   (let* ((sqrt-two (p08b3-sqrt (p08b3-two one)))
          (radius (p08b3-mul sqrt-two (p08b3-half one))))
     (and
      (p08b3-contains-radius-p radius zero one)
      (p08b3-is-upper-bound-p radius zero one)))))

(value-triple :itpeval-statement-checked)
:q
