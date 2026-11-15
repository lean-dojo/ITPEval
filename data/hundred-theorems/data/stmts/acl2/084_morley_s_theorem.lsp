;; Statement-only formalization of Hundred Theorems artifact 084, "Morley's
;; Theorem": the intersections of adjacent internal angle trisectors of a
;; nondegenerate plane triangle form an equilateral triangle.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Morley's conclusion and the selected-third-angle hypotheses are polynomial
;; in dot products, cross products, and order.  Conservative generic symbols
;; therefore preserve the real-coordinate theorem without restricting its
;; scalars to ACL2's executable rationals.  Every ordered-ring law used by the
;; statement remains an explicit hypothesis.
(defstub ht084-carrier (x) t)
(defstub ht084-add-op (x y) t)
(defstub ht084-multiply-op (x y) t)
(defstub ht084-negate-op (x) t)
(defstub ht084-less-op (x y) t)

(defun ht084-member-p (x)
  (if (ht084-carrier x) t nil))

(defun ht084-add (x y)
  (ht084-add-op x y))

(defun ht084-mul (x y)
  (ht084-multiply-op x y))

(defun ht084-neg (x)
  (ht084-negate-op x))

(defun ht084-sub (x y)
  (ht084-add x (ht084-neg y)))

(defun ht084-less (x y)
  (if (ht084-less-op x y) t nil))

(defun ht084-leq (x y)
  (not (ht084-less y x)))

(defun-sk ht084-ring-laws-p (zero one)
  (forall (x y z)
    (implies
     (and
      (ht084-member-p x)
      (ht084-member-p y)
      (ht084-member-p z))
     (and
      (ht084-member-p (ht084-add x y))
      (ht084-member-p (ht084-mul x y))
      (ht084-member-p (ht084-neg x))
      (equal (ht084-add (ht084-add x y) z)
             (ht084-add x (ht084-add y z)))
      (equal (ht084-add x y) (ht084-add y x))
      (equal (ht084-add x zero) x)
      (equal (ht084-add x (ht084-neg x)) zero)
      (equal (ht084-mul (ht084-mul x y) z)
             (ht084-mul x (ht084-mul y z)))
      (equal (ht084-mul x y) (ht084-mul y x))
      (equal (ht084-mul x one) x)
      (equal
       (ht084-mul x (ht084-add y z))
       (ht084-add (ht084-mul x y)
                  (ht084-mul x z)))))))

(defun-sk ht084-order-laws-p (zero)
  (forall (x y z)
    (implies
     (and
      (ht084-member-p x)
      (ht084-member-p y)
      (ht084-member-p z))
     (and
      (not (ht084-less x x))
      (or (equal x y)
          (ht084-less x y)
          (ht084-less y x))
      (implies
       (and (ht084-less x y)
            (ht084-less y z))
       (ht084-less x z))
      (implies
       (ht084-less x y)
       (ht084-less (ht084-add x z)
                   (ht084-add y z)))
      (implies
       (and (ht084-less zero x)
            (ht084-less zero y))
       (ht084-less zero (ht084-mul x y)))))))

(defun ht084-ordered-ring-p (zero one)
  (and
   (ht084-member-p zero)
   (ht084-member-p one)
   (not (equal zero one))
   (ht084-less zero one)
   (ht084-ring-laws-p zero one)
   (ht084-order-laws-p zero)))

(defun ht084-point-p (point)
  (and
   (true-listp point)
   (equal (len point) 2)
   (ht084-member-p (nth 0 point))
   (ht084-member-p (nth 1 point))))

(defun ht084-all-points-p (points)
  (if (consp points)
      (and
       (ht084-point-p (car points))
       (ht084-all-points-p (cdr points)))
    (equal points nil)))

(defun ht084-square (x)
  (ht084-mul x x))

(defun ht084-three (one)
  (ht084-add one (ht084-add one one)))

(defun ht084-four (one)
  (ht084-add (ht084-add one one)
             (ht084-add one one)))

(defun ht084-orientation (first second third)
  (ht084-sub
   (ht084-mul
    (ht084-sub (nth 0 second) (nth 0 first))
    (ht084-sub (nth 1 third) (nth 1 first)))
   (ht084-mul
    (ht084-sub (nth 1 second) (nth 1 first))
    (ht084-sub (nth 0 third) (nth 0 first)))))

(defun ht084-distance-squared (first second)
  (ht084-add
   (ht084-square
    (ht084-sub (nth 0 first) (nth 0 second)))
   (ht084-square
    (ht084-sub (nth 1 first) (nth 1 second)))))

(defun ht084-in-closed-triangle-p (zero point a b c)
  (let ((abc (ht084-orientation a b c))
        (abp (ht084-orientation a b point))
        (bcp (ht084-orientation b c point))
        (cap (ht084-orientation c a point)))
    (or (and (ht084-less zero abc)
             (ht084-leq zero abp)
             (ht084-leq zero bcp)
             (ht084-leq zero cap))
        (and (ht084-less abc zero)
             (ht084-leq abp zero)
             (ht084-leq bcp zero)
             (ht084-leq cap zero)))))

;; For rays u and w at V, conjugate(u)*w represents the directed angle from
;; u to w.  Cubing conjugate(u)*v gives that full angle exactly when v is an
;; angle trisector.  The strict sector conditions select the internal third.
(defun ht084-angle-third-p (zero one first vertex trisector third)
  (let* ((ux (ht084-sub (nth 0 first) (nth 0 vertex)))
         (uy (ht084-sub (nth 1 first) (nth 1 vertex)))
         (vx (ht084-sub (nth 0 trisector) (nth 0 vertex)))
         (vy (ht084-sub (nth 1 trisector) (nth 1 vertex)))
         (wx (ht084-sub (nth 0 third) (nth 0 vertex)))
         (wy (ht084-sub (nth 1 third) (nth 1 vertex)))
         (z-real (ht084-add (ht084-mul ux vx)
                            (ht084-mul uy vy)))
         (z-imag (ht084-sub (ht084-mul ux vy)
                            (ht084-mul uy vx)))
         (t-real (ht084-add (ht084-mul ux wx)
                            (ht084-mul uy wy)))
         (t-imag (ht084-sub (ht084-mul ux wy)
                            (ht084-mul uy wx)))
         (z-real-squared (ht084-square z-real))
         (z-imag-squared (ht084-square z-imag))
         (z-cubed-real
          (ht084-sub
           (ht084-mul z-real z-real-squared)
           (ht084-mul
            (ht084-three one)
            (ht084-mul z-real z-imag-squared))))
         (z-cubed-imag
          (ht084-sub
           (ht084-mul
            (ht084-three one)
            (ht084-mul z-real-squared z-imag))
           (ht084-mul z-imag z-imag-squared))))
    (and
     (ht084-less zero z-real)
     (ht084-less
      (ht084-add z-real-squared z-imag-squared)
      (ht084-mul (ht084-four one) z-real-squared))
     (equal
      (ht084-sub (ht084-mul z-cubed-real t-imag)
                 (ht084-mul z-cubed-imag t-real))
      zero)
     (ht084-less
      zero
      (ht084-add (ht084-mul z-cubed-real t-real)
                 (ht084-mul z-cubed-imag t-imag))))))

(defun hundred-theorems-084-morleys-theorem-statement
    (zero one a b c p q r)
  (implies
   (and
    (ht084-ordered-ring-p zero one)
    (ht084-all-points-p (list a b c p q r))
    (not (equal (ht084-orientation a b c) zero))
    (ht084-in-closed-triangle-p zero p a b c)
    (ht084-in-closed-triangle-p zero q a b c)
    (ht084-in-closed-triangle-p zero r a b c)
    (ht084-angle-third-p zero one a b r c)
    (ht084-angle-third-p zero one b a r c)
    (ht084-angle-third-p zero one b c p a)
    (ht084-angle-third-p zero one c b p a)
    (ht084-angle-third-p zero one c a q b)
    (ht084-angle-third-p zero one a c q b))
   (and
    (equal (ht084-distance-squared r p)
           (ht084-distance-squared p q))
    (equal (ht084-distance-squared q r)
           (ht084-distance-squared p q)))))

(value-triple :itpeval-statement-checked)
:q
