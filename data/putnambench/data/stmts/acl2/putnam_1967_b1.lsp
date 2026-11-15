;; Statement-only formalization of PutnamBench corpus artifact
;; putnam_1967_b1: alternating radius-length sides of a cyclically ordered
;; hexagon have the other three side midpoints forming an equilateral triangle.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; After replacing distances by squared distances and convex-hull interior by
;; positive barycentric coordinates, the source is a first-order formula over
;; real closed fields. A real counterexample therefore exists iff one exists
;; over the real algebraic numbers. One isolated algebraic number alpha and
;; rational functions of alpha encode every finite algebraic tuple.
;;
;; The six-point list is definitionally equivalent to the source function on
;; ZMod 6. The midpoint variables are eliminated by substitution. The circle
;; center and the nine segment-intersection witnesses occur existentially only
;; in the source antecedent, so
;;
;;   ((exists w, A(w)) implies C) iff (forall w, A(w) implies C).
;;
;; Free ACL2 arguments supply exactly this universal closure, without changing
;; the source quantifier scope. Positive barycentric coefficients characterize
;; ordinary convex-hull interior once a noncollinear triple makes the hull
;; full-dimensional.

;; Rational polynomials in alpha use descending coefficient order.

(defun putnam-1967-b1-rp-p (p)
  (if (consp p)
      (and (rationalp (car p))
           (putnam-1967-b1-rp-p (cdr p)))
    (equal p nil)))

(defun putnam-1967-b1-rp-normalize (p)
  (if (consp p)
      (if (equal (car p) 0)
          (putnam-1967-b1-rp-normalize (cdr p))
        p)
    nil))

(defun putnam-1967-b1-rp-neg (p)
  (if (consp p)
      (cons (- (car p))
            (putnam-1967-b1-rp-neg (cdr p)))
    nil))

(defun putnam-1967-b1-rp-add-raw (p q)
  (declare (xargs :measure (+ (acl2-count p) (acl2-count q))))
  (cond
   ((endp p) q)
   ((endp q) p)
   ((< (len p) (len q))
    (cons (car q)
          (putnam-1967-b1-rp-add-raw p (cdr q))))
   ((< (len q) (len p))
    (cons (car p)
          (putnam-1967-b1-rp-add-raw (cdr p) q)))
   (t
    (cons (+ (car p) (car q))
          (putnam-1967-b1-rp-add-raw (cdr p) (cdr q))))))

(defun putnam-1967-b1-rp-add (p q)
  (putnam-1967-b1-rp-normalize
   (putnam-1967-b1-rp-add-raw p q)))

(defun putnam-1967-b1-rp-sub (p q)
  (putnam-1967-b1-rp-add
   p (putnam-1967-b1-rp-neg q)))

(defun putnam-1967-b1-rp-scale (c p)
  (if (consp p)
      (cons (* c (car p))
            (putnam-1967-b1-rp-scale c (cdr p)))
    nil))

(defun putnam-1967-b1-zeroes (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      nil
    (cons 0 (putnam-1967-b1-zeroes (- n 1)))))

(defun putnam-1967-b1-rp-scale-shift (c p shift)
  (append (putnam-1967-b1-rp-scale c p)
          (putnam-1967-b1-zeroes shift)))

(defun putnam-1967-b1-rp-mul-raw (p q)
  (if (consp p)
      (putnam-1967-b1-rp-add
       (putnam-1967-b1-rp-scale-shift
        (car p) q (len (cdr p)))
       (putnam-1967-b1-rp-mul-raw (cdr p) q))
    nil))

(defun putnam-1967-b1-rp-mul (p q)
  (putnam-1967-b1-rp-normalize
   (putnam-1967-b1-rp-mul-raw p q)))

(defun putnam-1967-b1-rp-eval-aux (p x accumulator)
  (if (consp p)
      (putnam-1967-b1-rp-eval-aux
       (cdr p) x (+ (* accumulator x) (car p)))
    accumulator))

(defun putnam-1967-b1-rp-eval (p x)
  (putnam-1967-b1-rp-eval-aux p x 0))

(defun putnam-1967-b1-rp-derivative-aux (p degree)
  (if (consp p)
      (if (zp degree)
          nil
        (cons (* degree (car p))
              (putnam-1967-b1-rp-derivative-aux
               (cdr p) (- degree 1))))
    nil))

(defun putnam-1967-b1-rp-derivative (p)
  (let ((p (putnam-1967-b1-rp-normalize p)))
    (putnam-1967-b1-rp-normalize
     (putnam-1967-b1-rp-derivative-aux
      p (nfix (- (len p) 1))))))

(defun putnam-1967-b1-rp-rem-fuel (p q fuel)
  (declare (xargs :measure (nfix fuel)))
  (let ((p (putnam-1967-b1-rp-normalize p))
        (q (putnam-1967-b1-rp-normalize q)))
    (if (or (zp fuel)
            (endp q)
            (< (len p) (len q)))
        p
      (putnam-1967-b1-rp-rem-fuel
       (putnam-1967-b1-rp-sub
        p
        (putnam-1967-b1-rp-scale-shift
         (/ (car p) (car q))
         q
         (- (len p) (len q))))
       q
       (- fuel 1)))))

(defun putnam-1967-b1-rp-rem (p q)
  (putnam-1967-b1-rp-rem-fuel
   p q (+ 1 (len (putnam-1967-b1-rp-normalize p)))))

(defun putnam-1967-b1-rp-sturm-tail (previous current fuel)
  (declare (xargs :measure (nfix fuel)))
  (let ((current (putnam-1967-b1-rp-normalize current)))
    (if (or (zp fuel) (endp current))
        nil
      (cons
       current
       (putnam-1967-b1-rp-sturm-tail
        current
        (putnam-1967-b1-rp-neg
         (putnam-1967-b1-rp-rem previous current))
        (- fuel 1))))))

(defun putnam-1967-b1-rp-sturm-sequence (p q)
  (let ((p (putnam-1967-b1-rp-normalize p))
        (q (putnam-1967-b1-rp-normalize q)))
    (if (endp p)
        nil
      (cons
       p
       (if (endp q)
           nil
         (cons
          q
          (putnam-1967-b1-rp-sturm-tail
           p q (+ 1 (len p) (len q)))))))))

(defun putnam-1967-b1-rational-sign (x)
  (cond ((< x 0) -1)
        ((< 0 x) 1)
        (t 0)))

(defun putnam-1967-b1-rp-variations-aux
    (polynomials x previous-sign)
  (if (consp polynomials)
      (let ((sign
             (putnam-1967-b1-rational-sign
              (putnam-1967-b1-rp-eval (car polynomials) x))))
        (if (equal sign 0)
            (putnam-1967-b1-rp-variations-aux
             (cdr polynomials) x previous-sign)
          (+ (if (and (not (equal previous-sign 0))
                      (not (equal sign previous-sign)))
                 1
               0)
             (putnam-1967-b1-rp-variations-aux
              (cdr polynomials) x sign))))
    0))

(defun putnam-1967-b1-rp-variations (polynomials x)
  (putnam-1967-b1-rp-variations-aux polynomials x 0))

(defun putnam-1967-b1-rp-cauchy-index (p q lower upper)
  (let ((sequence
         (putnam-1967-b1-rp-sturm-sequence p q)))
    (- (putnam-1967-b1-rp-variations sequence lower)
       (putnam-1967-b1-rp-variations sequence upper))))

(defun putnam-1967-b1-rp-root-count (p lower upper)
  (putnam-1967-b1-rp-cauchy-index
   p (putnam-1967-b1-rp-derivative p) lower upper))

(defun putnam-1967-b1-primitive-p (primitive lower upper)
  (and
   (putnam-1967-b1-rp-p primitive)
   (consp (putnam-1967-b1-rp-normalize primitive))
   (rationalp lower)
   (rationalp upper)
   (< lower upper)
   (not (equal (putnam-1967-b1-rp-eval primitive lower) 0))
   (not (equal (putnam-1967-b1-rp-eval primitive upper) 0))
   (equal
    (putnam-1967-b1-rp-root-count primitive lower upper)
    1)
   (not
    (equal
     (putnam-1967-b1-rp-cauchy-index
      primitive
      (putnam-1967-b1-rp-mul
       (putnam-1967-b1-rp-derivative primitive)
       (putnam-1967-b1-rp-derivative primitive))
      lower
      upper)
     0))))

;; The Sturm-Tarski query over the isolated root alpha is sign(g(alpha)).
(defun putnam-1967-b1-alg-sign
    (primitive lower upper g)
  (putnam-1967-b1-rp-cauchy-index
   primitive
   (putnam-1967-b1-rp-mul
    (putnam-1967-b1-rp-derivative primitive)
    g)
   lower
   upper))

;; A field element is (numerator denominator), evaluated at alpha.

(defun putnam-1967-b1-rf-numerator (value)
  (car value))

(defun putnam-1967-b1-rf-denominator (value)
  (cadr value))

(defun putnam-1967-b1-rf-code-p
    (primitive lower upper value)
  (and
   (true-listp value)
   (equal (len value) 2)
   (putnam-1967-b1-rp-p
    (putnam-1967-b1-rf-numerator value))
   (putnam-1967-b1-rp-p
    (putnam-1967-b1-rf-denominator value))
   (not
    (equal
     (putnam-1967-b1-alg-sign
      primitive lower upper
      (putnam-1967-b1-rf-denominator value))
     0))))

(defun putnam-1967-b1-rf-list-p
    (primitive lower upper values)
  (if (consp values)
      (and
       (putnam-1967-b1-rf-code-p
        primitive lower upper (car values))
       (putnam-1967-b1-rf-list-p
        primitive lower upper (cdr values)))
    (equal values nil)))

(defun putnam-1967-b1-rf-zero ()
  (list nil (list 1)))

(defun putnam-1967-b1-rf-one ()
  (list (list 1) (list 1)))

(defun putnam-1967-b1-rf-neg (value)
  (list
   (putnam-1967-b1-rp-neg
    (putnam-1967-b1-rf-numerator value))
   (putnam-1967-b1-rf-denominator value)))

(defun putnam-1967-b1-rf-add (left right)
  (list
   (putnam-1967-b1-rp-add
    (putnam-1967-b1-rp-mul
     (putnam-1967-b1-rf-numerator left)
     (putnam-1967-b1-rf-denominator right))
    (putnam-1967-b1-rp-mul
     (putnam-1967-b1-rf-numerator right)
     (putnam-1967-b1-rf-denominator left)))
   (putnam-1967-b1-rp-mul
    (putnam-1967-b1-rf-denominator left)
    (putnam-1967-b1-rf-denominator right))))

(defun putnam-1967-b1-rf-sub (left right)
  (putnam-1967-b1-rf-add
   left (putnam-1967-b1-rf-neg right)))

(defun putnam-1967-b1-rf-mul (left right)
  (list
   (putnam-1967-b1-rp-mul
    (putnam-1967-b1-rf-numerator left)
    (putnam-1967-b1-rf-numerator right))
   (putnam-1967-b1-rp-mul
    (putnam-1967-b1-rf-denominator left)
    (putnam-1967-b1-rf-denominator right))))

(defun putnam-1967-b1-rf-sign
    (primitive lower upper value)
  (putnam-1967-b1-alg-sign
   primitive lower upper
   (putnam-1967-b1-rp-mul
    (putnam-1967-b1-rf-numerator value)
    (putnam-1967-b1-rf-denominator value))))

(defun putnam-1967-b1-rf-equal-p
    (primitive lower upper left right)
  (equal
   (putnam-1967-b1-rf-sign
    primitive lower upper
    (putnam-1967-b1-rf-sub left right))
   0))

(defun putnam-1967-b1-rf-positive-p
    (primitive lower upper value)
  (equal
   (putnam-1967-b1-rf-sign
    primitive lower upper value)
   1))

(defun putnam-1967-b1-rf-nonnegative-p
    (primitive lower upper value)
  (not
   (equal
    (putnam-1967-b1-rf-sign
     primitive lower upper value)
    -1)))

(defun putnam-1967-b1-point-code-p
    (primitive lower upper point)
  (and
   (true-listp point)
   (equal (len point) 2)
   (putnam-1967-b1-rf-list-p
    primitive lower upper point)))

(defun putnam-1967-b1-point-list-p
    (primitive lower upper points)
  (if (consp points)
      (and
       (putnam-1967-b1-point-code-p
        primitive lower upper (car points))
       (putnam-1967-b1-point-list-p
        primitive lower upper (cdr points)))
    (equal points nil)))

(defun putnam-1967-b1-witness-code-p
    (primitive lower upper witness)
  (and
   (true-listp witness)
   (equal (len witness) 7)
   (putnam-1967-b1-rf-list-p
    primitive lower upper witness)))

(defun putnam-1967-b1-witness-list-p
    (primitive lower upper witnesses)
  (if (consp witnesses)
      (and
       (putnam-1967-b1-witness-code-p
        primitive lower upper (car witnesses))
       (putnam-1967-b1-witness-list-p
        primitive lower upper (cdr witnesses)))
    (equal witnesses nil)))

(defun putnam-1967-b1-rf-square (value)
  (putnam-1967-b1-rf-mul value value))

(defun putnam-1967-b1-distance-squared (left right)
  (putnam-1967-b1-rf-add
   (putnam-1967-b1-rf-square
    (putnam-1967-b1-rf-sub (nth 0 left) (nth 0 right)))
   (putnam-1967-b1-rf-square
    (putnam-1967-b1-rf-sub (nth 1 left) (nth 1 right)))))

(defun putnam-1967-b1-orientation (a b c)
  (putnam-1967-b1-rf-sub
   (putnam-1967-b1-rf-mul
    (putnam-1967-b1-rf-sub (nth 0 b) (nth 0 a))
    (putnam-1967-b1-rf-sub (nth 1 c) (nth 1 a)))
   (putnam-1967-b1-rf-mul
    (putnam-1967-b1-rf-sub (nth 1 b) (nth 1 a))
    (putnam-1967-b1-rf-sub (nth 0 c) (nth 0 a)))))

(defun putnam-1967-b1-noncollinear-with-pair-p
    (primitive lower upper a b remaining)
  (if (consp remaining)
      (or
       (not
        (equal
         (putnam-1967-b1-rf-sign
          primitive lower upper
          (putnam-1967-b1-orientation a b (car remaining)))
         0))
       (putnam-1967-b1-noncollinear-with-pair-p
        primitive lower upper a b (cdr remaining)))
    nil))

(defun putnam-1967-b1-noncollinear-with-first-p
    (primitive lower upper a remaining)
  (if (consp remaining)
      (or
       (putnam-1967-b1-noncollinear-with-pair-p
        primitive lower upper a (car remaining) (cdr remaining))
       (putnam-1967-b1-noncollinear-with-first-p
        primitive lower upper a (cdr remaining)))
    nil))

(defun putnam-1967-b1-full-dimensional-p
    (primitive lower upper points)
  (if (consp points)
      (or
       (putnam-1967-b1-noncollinear-with-first-p
        primitive lower upper (car points) (cdr points))
       (putnam-1967-b1-full-dimensional-p
        primitive lower upper (cdr points)))
    nil))

(defun putnam-1967-b1-all-on-circle-p
    (primitive lower upper center radius-squared points)
  (if (consp points)
      (and
       (putnam-1967-b1-rf-equal-p
        primitive lower upper
        (putnam-1967-b1-distance-squared center (car points))
        radius-squared)
       (putnam-1967-b1-all-on-circle-p
        primitive lower upper center radius-squared (cdr points)))
    t))

(defun putnam-1967-b1-positive-list-p
    (primitive lower upper values)
  (if (consp values)
      (and
       (putnam-1967-b1-rf-positive-p
        primitive lower upper (car values))
       (putnam-1967-b1-positive-list-p
        primitive lower upper (cdr values)))
    t))

(defun putnam-1967-b1-rf-sum (values)
  (if (consp values)
      (putnam-1967-b1-rf-add
       (car values)
       (putnam-1967-b1-rf-sum (cdr values)))
    (putnam-1967-b1-rf-zero)))

(defun putnam-1967-b1-weighted-coordinate-sum
    (weights points coordinate)
  (if (and (consp weights) (consp points))
      (putnam-1967-b1-rf-add
       (putnam-1967-b1-rf-mul
        (car weights)
        (nth coordinate (car points)))
       (putnam-1967-b1-weighted-coordinate-sum
        (cdr weights) (cdr points) coordinate))
    (putnam-1967-b1-rf-zero)))

(defun putnam-1967-b1-segment-coordinate
    (left right parameter coordinate)
  (putnam-1967-b1-rf-add
   (putnam-1967-b1-rf-mul
    (putnam-1967-b1-rf-sub
     (putnam-1967-b1-rf-one)
     parameter)
    (nth coordinate left))
   (putnam-1967-b1-rf-mul
    parameter
    (nth coordinate right))))

(defun putnam-1967-b1-interior-segment-witness-p
    (primitive lower upper points left-index right-index witness)
  (let* ((parameter (nth 0 witness))
         (weights (cdr witness))
         (left (nth left-index points))
         (right (nth right-index points))
         (one-minus-parameter
          (putnam-1967-b1-rf-sub
           (putnam-1967-b1-rf-one)
           parameter)))
    (and
     (putnam-1967-b1-rf-nonnegative-p
      primitive lower upper parameter)
     (putnam-1967-b1-rf-nonnegative-p
      primitive lower upper one-minus-parameter)
     (putnam-1967-b1-positive-list-p
      primitive lower upper weights)
     (putnam-1967-b1-rf-equal-p
      primitive lower upper
      (putnam-1967-b1-rf-sum weights)
      (putnam-1967-b1-rf-one))
     (putnam-1967-b1-rf-equal-p
      primitive lower upper
      (putnam-1967-b1-segment-coordinate
       left right parameter 0)
      (putnam-1967-b1-weighted-coordinate-sum
       weights points 0))
     (putnam-1967-b1-rf-equal-p
      primitive lower upper
      (putnam-1967-b1-segment-coordinate
       left right parameter 1)
      (putnam-1967-b1-weighted-coordinate-sum
       weights points 1)))))

(defun putnam-1967-b1-cyclic-order-witnesses-p
    (primitive lower upper points witnesses)
  (and
   (putnam-1967-b1-interior-segment-witness-p
    primitive lower upper points 0 2 (nth 0 witnesses))
   (putnam-1967-b1-interior-segment-witness-p
    primitive lower upper points 0 3 (nth 1 witnesses))
   (putnam-1967-b1-interior-segment-witness-p
    primitive lower upper points 0 4 (nth 2 witnesses))
   (putnam-1967-b1-interior-segment-witness-p
    primitive lower upper points 1 3 (nth 3 witnesses))
   (putnam-1967-b1-interior-segment-witness-p
    primitive lower upper points 1 4 (nth 4 witnesses))
   (putnam-1967-b1-interior-segment-witness-p
    primitive lower upper points 1 5 (nth 5 witnesses))
   (putnam-1967-b1-interior-segment-witness-p
    primitive lower upper points 2 4 (nth 6 witnesses))
   (putnam-1967-b1-interior-segment-witness-p
    primitive lower upper points 2 5 (nth 7 witnesses))
   (putnam-1967-b1-interior-segment-witness-p
    primitive lower upper points 3 5 (nth 8 witnesses))))

(defun putnam-1967-b1-points-distinct-p
    (primitive lower upper left right)
  (or
   (not
    (putnam-1967-b1-rf-equal-p
     primitive lower upper (nth 0 left) (nth 0 right)))
   (not
    (putnam-1967-b1-rf-equal-p
     primitive lower upper (nth 1 left) (nth 1 right)))))

;; This is four times the squared distance between the two midpoints.
(defun putnam-1967-b1-midpoint-distance-numerator
    (first-a first-b second-a second-b)
  (putnam-1967-b1-rf-add
   (putnam-1967-b1-rf-square
    (putnam-1967-b1-rf-sub
     (putnam-1967-b1-rf-add (nth 0 first-a) (nth 0 first-b))
     (putnam-1967-b1-rf-add (nth 0 second-a) (nth 0 second-b))))
   (putnam-1967-b1-rf-square
    (putnam-1967-b1-rf-sub
     (putnam-1967-b1-rf-add (nth 1 first-a) (nth 1 first-b))
     (putnam-1967-b1-rf-add (nth 1 second-a) (nth 1 second-b))))))

(defun putnambench-putnam-1967-b1-statement
    (primitive lower upper radius center points witnesses)
  (let* ((radius-squared
          (putnam-1967-b1-rf-square radius))
         (l0 (nth 0 points))
         (l1 (nth 1 points))
         (l2 (nth 2 points))
         (l3 (nth 3 points))
         (l4 (nth 4 points))
         (l5 (nth 5 points))
         (pq
          (putnam-1967-b1-midpoint-distance-numerator
           l1 l2 l3 l4))
         (rp
          (putnam-1967-b1-midpoint-distance-numerator
           l5 l0 l1 l2))
         (qr
          (putnam-1967-b1-midpoint-distance-numerator
           l3 l4 l5 l0)))
    (implies
     (and
      (putnam-1967-b1-primitive-p primitive lower upper)
      (putnam-1967-b1-rf-code-p
       primitive lower upper radius)
      (putnam-1967-b1-point-code-p
       primitive lower upper center)
      (true-listp points)
      (equal (len points) 6)
      (putnam-1967-b1-point-list-p
       primitive lower upper points)
      (true-listp witnesses)
      (equal (len witnesses) 9)
      (putnam-1967-b1-witness-list-p
       primitive lower upper witnesses)
      (putnam-1967-b1-rf-positive-p
       primitive lower upper radius)
      (putnam-1967-b1-full-dimensional-p
       primitive lower upper points)
      (putnam-1967-b1-all-on-circle-p
       primitive lower upper center radius-squared points)
      (putnam-1967-b1-cyclic-order-witnesses-p
       primitive lower upper points witnesses)
      (putnam-1967-b1-rf-equal-p
       primitive lower upper
       (putnam-1967-b1-distance-squared l0 l1)
       radius-squared)
      (putnam-1967-b1-rf-equal-p
       primitive lower upper
       (putnam-1967-b1-distance-squared l2 l3)
       radius-squared)
      (putnam-1967-b1-rf-equal-p
       primitive lower upper
       (putnam-1967-b1-distance-squared l4 l5)
       radius-squared)
      (putnam-1967-b1-points-distinct-p
       primitive lower upper l1 l2)
      (putnam-1967-b1-points-distinct-p
       primitive lower upper l3 l4)
      (putnam-1967-b1-points-distinct-p
       primitive lower upper l5 l0))
     (and
      (putnam-1967-b1-rf-equal-p
       primitive lower upper pq rp)
      (putnam-1967-b1-rf-equal-p
       primitive lower upper qr pq)))))

(value-triple :itpeval-statement-checked)
:q
