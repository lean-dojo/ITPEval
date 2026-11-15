;; Statement-only formalization of PutnamBench corpus artifact putnam_1974_b1:
;; five points on the Euclidean unit circle maximize the sum of their ten
;; pairwise distances exactly when they are the five distinct vertices of a
;; regular pentagon, equivalently when some cyclic ordering of the distinct
;; points has equal positive consecutive distances. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; After introducing a nonnegative variable for each Euclidean distance, the
;; source statement is first-order over real closed fields. Its validity over
;; the reals is therefore equivalent to validity over the real algebraic
;; numbers. One isolated algebraic number alpha and rational functions of
;; alpha encode every finite tuple of real algebraic coordinates and distances.
;;
;; Write M(p) for maximality and R(p) for the distinct equal-edge cyclic-order
;; condition characterizing the vertices of a regular pentagon. The source
;; equivalence M(p) <-> R(p) is represented by the equivalent pair
;;
;;   R(p) -> every unit-circle q has S(q) <= S(p),
;;   not R(p) -> S(p) < S(r) for every unit-circle r satisfying R(r).
;;
;; A regular unit-circle r exists. Hence the second clause says exactly that a
;; nonregular p is not maximal; conversely, the source equivalence makes every
;; such r maximal and therefore strictly better than any nonmaximal p. Free
;; ACL2 arguments provide the universal p, q, and r quantifiers. The finite
;; existential cyclic ordering is searched internally over all permutations.

;; Rational polynomials in alpha use descending coefficient order.

(defun putnam-1974-b1-rp-p (p)
  (if (consp p)
      (and (rationalp (car p))
           (putnam-1974-b1-rp-p (cdr p)))
    (equal p nil)))

(defun putnam-1974-b1-rp-normalize (p)
  (if (consp p)
      (if (equal (car p) 0)
          (putnam-1974-b1-rp-normalize (cdr p))
        p)
    nil))

(defun putnam-1974-b1-rp-neg (p)
  (if (consp p)
      (cons (- (car p))
            (putnam-1974-b1-rp-neg (cdr p)))
    nil))

(defun putnam-1974-b1-rp-add-raw (p q)
  (declare (xargs :measure (+ (acl2-count p) (acl2-count q))))
  (cond
   ((endp p) q)
   ((endp q) p)
   ((< (len p) (len q))
    (cons (car q)
          (putnam-1974-b1-rp-add-raw p (cdr q))))
   ((< (len q) (len p))
    (cons (car p)
          (putnam-1974-b1-rp-add-raw (cdr p) q)))
   (t
    (cons (+ (car p) (car q))
          (putnam-1974-b1-rp-add-raw (cdr p) (cdr q))))))

(defun putnam-1974-b1-rp-add (p q)
  (putnam-1974-b1-rp-normalize
   (putnam-1974-b1-rp-add-raw p q)))

(defun putnam-1974-b1-rp-sub (p q)
  (putnam-1974-b1-rp-add
   p (putnam-1974-b1-rp-neg q)))

(defun putnam-1974-b1-rp-scale (c p)
  (if (consp p)
      (cons (* c (car p))
            (putnam-1974-b1-rp-scale c (cdr p)))
    nil))

(defun putnam-1974-b1-zeroes (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      nil
    (cons 0 (putnam-1974-b1-zeroes (- n 1)))))

(defun putnam-1974-b1-rp-scale-shift (c p shift)
  (append (putnam-1974-b1-rp-scale c p)
          (putnam-1974-b1-zeroes shift)))

(defun putnam-1974-b1-rp-mul-raw (p q)
  (if (consp p)
      (putnam-1974-b1-rp-add
       (putnam-1974-b1-rp-scale-shift
        (car p) q (len (cdr p)))
       (putnam-1974-b1-rp-mul-raw (cdr p) q))
    nil))

(defun putnam-1974-b1-rp-mul (p q)
  (putnam-1974-b1-rp-normalize
   (putnam-1974-b1-rp-mul-raw p q)))

(defun putnam-1974-b1-rp-eval-aux (p x accumulator)
  (if (consp p)
      (putnam-1974-b1-rp-eval-aux
       (cdr p) x (+ (* accumulator x) (car p)))
    accumulator))

(defun putnam-1974-b1-rp-eval (p x)
  (putnam-1974-b1-rp-eval-aux p x 0))

(defun putnam-1974-b1-rp-derivative-aux (p degree)
  (if (consp p)
      (if (zp degree)
          nil
        (cons (* degree (car p))
              (putnam-1974-b1-rp-derivative-aux
               (cdr p) (- degree 1))))
    nil))

(defun putnam-1974-b1-rp-derivative (p)
  (let ((p (putnam-1974-b1-rp-normalize p)))
    (putnam-1974-b1-rp-normalize
     (putnam-1974-b1-rp-derivative-aux
      p (nfix (- (len p) 1))))))

(defun putnam-1974-b1-rp-rem-fuel (p q fuel)
  (declare (xargs :measure (nfix fuel)))
  (let ((p (putnam-1974-b1-rp-normalize p))
        (q (putnam-1974-b1-rp-normalize q)))
    (if (or (zp fuel)
            (endp q)
            (< (len p) (len q)))
        p
      (putnam-1974-b1-rp-rem-fuel
       (putnam-1974-b1-rp-sub
        p
        (putnam-1974-b1-rp-scale-shift
         (/ (car p) (car q))
         q
         (- (len p) (len q))))
       q
       (- fuel 1)))))

(defun putnam-1974-b1-rp-rem (p q)
  (putnam-1974-b1-rp-rem-fuel
   p q (+ 1 (len (putnam-1974-b1-rp-normalize p)))))

(defun putnam-1974-b1-rp-sturm-tail (previous current fuel)
  (declare (xargs :measure (nfix fuel)))
  (let ((current (putnam-1974-b1-rp-normalize current)))
    (if (or (zp fuel) (endp current))
        nil
      (cons
       current
       (putnam-1974-b1-rp-sturm-tail
        current
        (putnam-1974-b1-rp-neg
         (putnam-1974-b1-rp-rem previous current))
        (- fuel 1))))))

(defun putnam-1974-b1-rp-sturm-sequence (p q)
  (let ((p (putnam-1974-b1-rp-normalize p))
        (q (putnam-1974-b1-rp-normalize q)))
    (if (endp p)
        nil
      (cons
       p
       (if (endp q)
           nil
         (cons
          q
          (putnam-1974-b1-rp-sturm-tail
           p q (+ 1 (len p) (len q)))))))))

(defun putnam-1974-b1-rational-sign (x)
  (cond ((< x 0) -1)
        ((< 0 x) 1)
        (t 0)))

(defun putnam-1974-b1-rp-variations-aux
    (polynomials x previous-sign)
  (if (consp polynomials)
      (let ((sign
             (putnam-1974-b1-rational-sign
              (putnam-1974-b1-rp-eval (car polynomials) x))))
        (if (equal sign 0)
            (putnam-1974-b1-rp-variations-aux
             (cdr polynomials) x previous-sign)
          (+ (if (and (not (equal previous-sign 0))
                      (not (equal sign previous-sign)))
                 1
               0)
             (putnam-1974-b1-rp-variations-aux
              (cdr polynomials) x sign))))
    0))

(defun putnam-1974-b1-rp-variations (polynomials x)
  (putnam-1974-b1-rp-variations-aux polynomials x 0))

(defun putnam-1974-b1-rp-cauchy-index (p q lower upper)
  (let ((sequence
         (putnam-1974-b1-rp-sturm-sequence p q)))
    (- (putnam-1974-b1-rp-variations sequence lower)
       (putnam-1974-b1-rp-variations sequence upper))))

(defun putnam-1974-b1-rp-root-count (p lower upper)
  (putnam-1974-b1-rp-cauchy-index
   p (putnam-1974-b1-rp-derivative p) lower upper))

(defun putnam-1974-b1-primitive-p (primitive lower upper)
  (and
   (putnam-1974-b1-rp-p primitive)
   (consp (putnam-1974-b1-rp-normalize primitive))
   (rationalp lower)
   (rationalp upper)
   (< lower upper)
   (not (equal (putnam-1974-b1-rp-eval primitive lower) 0))
   (not (equal (putnam-1974-b1-rp-eval primitive upper) 0))
   (equal
    (putnam-1974-b1-rp-root-count primitive lower upper)
    1)
   (not
    (equal
     (putnam-1974-b1-rp-cauchy-index
      primitive
      (putnam-1974-b1-rp-mul
       (putnam-1974-b1-rp-derivative primitive)
       (putnam-1974-b1-rp-derivative primitive))
      lower
      upper)
     0))))

;; The Sturm-Tarski query over the isolated root alpha is sign(g(alpha)).
(defun putnam-1974-b1-alg-sign
    (primitive lower upper g)
  (putnam-1974-b1-rp-cauchy-index
   primitive
   (putnam-1974-b1-rp-mul
    (putnam-1974-b1-rp-derivative primitive)
    g)
   lower
   upper))

;; A field element is (numerator denominator), evaluated at alpha.

(defun putnam-1974-b1-rf-numerator (value)
  (car value))

(defun putnam-1974-b1-rf-denominator (value)
  (cadr value))

(defun putnam-1974-b1-rf-code-p
    (primitive lower upper value)
  (and
   (true-listp value)
   (equal (len value) 2)
   (putnam-1974-b1-rp-p
    (putnam-1974-b1-rf-numerator value))
   (putnam-1974-b1-rp-p
    (putnam-1974-b1-rf-denominator value))
   (not
    (equal
     (putnam-1974-b1-alg-sign
      primitive lower upper
      (putnam-1974-b1-rf-denominator value))
     0))))

(defun putnam-1974-b1-rf-list-p
    (primitive lower upper values)
  (if (consp values)
      (and
       (putnam-1974-b1-rf-code-p
        primitive lower upper (car values))
       (putnam-1974-b1-rf-list-p
        primitive lower upper (cdr values)))
    (equal values nil)))

(defun putnam-1974-b1-rf-zero ()
  (list nil (list 1)))

(defun putnam-1974-b1-rf-one ()
  (list (list 1) (list 1)))

(defun putnam-1974-b1-rf-neg (value)
  (list
   (putnam-1974-b1-rp-neg
    (putnam-1974-b1-rf-numerator value))
   (putnam-1974-b1-rf-denominator value)))

(defun putnam-1974-b1-rf-add (left right)
  (list
   (putnam-1974-b1-rp-add
    (putnam-1974-b1-rp-mul
     (putnam-1974-b1-rf-numerator left)
     (putnam-1974-b1-rf-denominator right))
    (putnam-1974-b1-rp-mul
     (putnam-1974-b1-rf-numerator right)
     (putnam-1974-b1-rf-denominator left)))
   (putnam-1974-b1-rp-mul
    (putnam-1974-b1-rf-denominator left)
    (putnam-1974-b1-rf-denominator right))))

(defun putnam-1974-b1-rf-sub (left right)
  (putnam-1974-b1-rf-add
   left (putnam-1974-b1-rf-neg right)))

(defun putnam-1974-b1-rf-mul (left right)
  (list
   (putnam-1974-b1-rp-mul
    (putnam-1974-b1-rf-numerator left)
    (putnam-1974-b1-rf-numerator right))
   (putnam-1974-b1-rp-mul
    (putnam-1974-b1-rf-denominator left)
    (putnam-1974-b1-rf-denominator right))))

(defun putnam-1974-b1-rf-sign
    (primitive lower upper value)
  (putnam-1974-b1-alg-sign
   primitive lower upper
   (putnam-1974-b1-rp-mul
    (putnam-1974-b1-rf-numerator value)
    (putnam-1974-b1-rf-denominator value))))

(defun putnam-1974-b1-rf-equal-p
    (primitive lower upper left right)
  (equal
   (putnam-1974-b1-rf-sign
    primitive lower upper
    (putnam-1974-b1-rf-sub left right))
   0))

(defun putnam-1974-b1-rf-positive-p
    (primitive lower upper value)
  (equal
   (putnam-1974-b1-rf-sign
    primitive lower upper value)
   1))

(defun putnam-1974-b1-rf-nonnegative-p
    (primitive lower upper value)
  (not
   (equal
    (putnam-1974-b1-rf-sign
     primitive lower upper value)
    -1)))

(defun putnam-1974-b1-point-code-p
    (primitive lower upper point)
  (and
   (true-listp point)
   (equal (len point) 2)
   (putnam-1974-b1-rf-list-p
    primitive lower upper point)))

(defun putnam-1974-b1-point-list-p
    (primitive lower upper points)
  (if (consp points)
      (and
       (putnam-1974-b1-point-code-p
        primitive lower upper (car points))
       (putnam-1974-b1-point-list-p
        primitive lower upper (cdr points)))
    (equal points nil)))

(defun putnam-1974-b1-rf-square (value)
  (putnam-1974-b1-rf-mul value value))

(defun putnam-1974-b1-distance-squared (left right)
  (putnam-1974-b1-rf-add
   (putnam-1974-b1-rf-square
    (putnam-1974-b1-rf-sub (nth 0 left) (nth 0 right)))
   (putnam-1974-b1-rf-square
    (putnam-1974-b1-rf-sub (nth 1 left) (nth 1 right)))))

(defun putnam-1974-b1-point-equal-p
    (primitive lower upper left right)
  (and
   (putnam-1974-b1-rf-equal-p
    primitive lower upper (nth 0 left) (nth 0 right))
   (putnam-1974-b1-rf-equal-p
    primitive lower upper (nth 1 left) (nth 1 right))))

(defun putnam-1974-b1-point-distinct-from-list-p
    (primitive lower upper point points)
  (if (consp points)
      (and
       (not
        (putnam-1974-b1-point-equal-p
         primitive lower upper point (car points)))
       (putnam-1974-b1-point-distinct-from-list-p
        primitive lower upper point (cdr points)))
    t))

(defun putnam-1974-b1-distinct-point-list-p
    (primitive lower upper points)
  (if (consp points)
      (and
       (putnam-1974-b1-point-distinct-from-list-p
        primitive lower upper (car points) (cdr points))
       (putnam-1974-b1-distinct-point-list-p
        primitive lower upper (cdr points)))
    t))

(defun putnam-1974-b1-unit-point-p
    (primitive lower upper point)
  (putnam-1974-b1-rf-equal-p
   primitive lower upper
   (putnam-1974-b1-rf-add
    (putnam-1974-b1-rf-square (nth 0 point))
    (putnam-1974-b1-rf-square (nth 1 point)))
   (putnam-1974-b1-rf-one)))

(defun putnam-1974-b1-unit-points-p
    (primitive lower upper points)
  (if (consp points)
      (and
       (putnam-1974-b1-unit-point-p
        primitive lower upper (car points))
       (putnam-1974-b1-unit-points-p
        primitive lower upper (cdr points)))
    t))

(defun putnam-1974-b1-distance-value-p
    (primitive lower upper left right value)
  (and
   (putnam-1974-b1-rf-nonnegative-p
    primitive lower upper value)
   (putnam-1974-b1-rf-equal-p
    primitive lower upper
    (putnam-1974-b1-rf-square value)
    (putnam-1974-b1-distance-squared left right))))

;; DISTANCES is ordered as 01, 02, 03, 04, 12, 13, 14, 23, 24, 34.
(defun putnam-1974-b1-distance-list-p
    (primitive lower upper points distances)
  (and
   (true-listp distances)
   (equal (len distances) 10)
   (putnam-1974-b1-rf-list-p
    primitive lower upper distances)
   (putnam-1974-b1-distance-value-p
    primitive lower upper (nth 0 points) (nth 1 points) (nth 0 distances))
   (putnam-1974-b1-distance-value-p
    primitive lower upper (nth 0 points) (nth 2 points) (nth 1 distances))
   (putnam-1974-b1-distance-value-p
    primitive lower upper (nth 0 points) (nth 3 points) (nth 2 distances))
   (putnam-1974-b1-distance-value-p
    primitive lower upper (nth 0 points) (nth 4 points) (nth 3 distances))
   (putnam-1974-b1-distance-value-p
    primitive lower upper (nth 1 points) (nth 2 points) (nth 4 distances))
   (putnam-1974-b1-distance-value-p
    primitive lower upper (nth 1 points) (nth 3 points) (nth 5 distances))
   (putnam-1974-b1-distance-value-p
    primitive lower upper (nth 1 points) (nth 4 points) (nth 6 distances))
   (putnam-1974-b1-distance-value-p
    primitive lower upper (nth 2 points) (nth 3 points) (nth 7 distances))
   (putnam-1974-b1-distance-value-p
    primitive lower upper (nth 2 points) (nth 4 points) (nth 8 distances))
   (putnam-1974-b1-distance-value-p
    primitive lower upper (nth 3 points) (nth 4 points) (nth 9 distances))))

(defun putnam-1974-b1-rf-sum (values)
  (if (consp values)
      (putnam-1974-b1-rf-add
       (car values)
       (putnam-1974-b1-rf-sum (cdr values)))
    (putnam-1974-b1-rf-zero)))

(defun putnam-1974-b1-cons-to-each (value lists)
  (if (consp lists)
      (cons (cons value (car lists))
            (putnam-1974-b1-cons-to-each value (cdr lists)))
    nil))

(defun putnam-1974-b1-insert-everywhere (value values)
  (if (consp values)
      (cons
       (cons value values)
       (putnam-1974-b1-cons-to-each
        (car values)
        (putnam-1974-b1-insert-everywhere value (cdr values))))
    (list (list value))))

(defun putnam-1974-b1-insert-into-all (value lists)
  (if (consp lists)
      (append
       (putnam-1974-b1-insert-everywhere value (car lists))
       (putnam-1974-b1-insert-into-all value (cdr lists)))
    nil))

(defun putnam-1974-b1-permutations (values)
  (if (consp values)
      (putnam-1974-b1-insert-into-all
       (car values)
       (putnam-1974-b1-permutations (cdr values)))
    (list nil)))

(defun putnam-1974-b1-regular-order-p
    (primitive lower upper ordered-points)
  (let ((edge
         (putnam-1974-b1-distance-squared
          (nth 0 ordered-points) (nth 1 ordered-points))))
    (and
     (putnam-1974-b1-distinct-point-list-p
      primitive lower upper ordered-points)
     (putnam-1974-b1-rf-positive-p
      primitive lower upper edge)
     (putnam-1974-b1-rf-equal-p
      primitive lower upper edge
      (putnam-1974-b1-distance-squared
       (nth 1 ordered-points) (nth 2 ordered-points)))
     (putnam-1974-b1-rf-equal-p
      primitive lower upper edge
      (putnam-1974-b1-distance-squared
       (nth 2 ordered-points) (nth 3 ordered-points)))
     (putnam-1974-b1-rf-equal-p
      primitive lower upper edge
      (putnam-1974-b1-distance-squared
       (nth 3 ordered-points) (nth 4 ordered-points)))
     (putnam-1974-b1-rf-equal-p
      primitive lower upper edge
      (putnam-1974-b1-distance-squared
       (nth 4 ordered-points) (nth 0 ordered-points))))))

(defun putnam-1974-b1-regular-permutation-exists-p
    (primitive lower upper permutations)
  (if (consp permutations)
      (or
       (putnam-1974-b1-regular-order-p
        primitive lower upper (car permutations))
       (putnam-1974-b1-regular-permutation-exists-p
        primitive lower upper (cdr permutations)))
    nil))

(defun putnam-1974-b1-regular-p
    (primitive lower upper points)
  (putnam-1974-b1-regular-permutation-exists-p
   primitive lower upper
   (putnam-1974-b1-permutations points)))

(defun putnam-1974-b1-configuration-code-p
    (primitive lower upper points distances)
  (and
   (true-listp points)
   (equal (len points) 5)
   (putnam-1974-b1-point-list-p
    primitive lower upper points)
   (putnam-1974-b1-distance-list-p
    primitive lower upper points distances)))

(defun putnambench-putnam-1974-b1-statement
    (primitive lower upper
     points point-distances
     competitor competitor-distances
     regular-reference regular-reference-distances)
  (implies
   (and
    (putnam-1974-b1-primitive-p primitive lower upper)
    (putnam-1974-b1-configuration-code-p
     primitive lower upper points point-distances)
    (putnam-1974-b1-configuration-code-p
     primitive lower upper competitor competitor-distances)
    (putnam-1974-b1-configuration-code-p
     primitive lower upper
     regular-reference regular-reference-distances))
   (and
    (implies
     (and
      (putnam-1974-b1-unit-points-p
       primitive lower upper points)
      (putnam-1974-b1-regular-p
       primitive lower upper points)
      (putnam-1974-b1-unit-points-p
       primitive lower upper competitor))
     (putnam-1974-b1-rf-nonnegative-p
      primitive lower upper
      (putnam-1974-b1-rf-sub
       (putnam-1974-b1-rf-sum point-distances)
       (putnam-1974-b1-rf-sum competitor-distances))))
    (implies
     (and
      (putnam-1974-b1-unit-points-p
       primitive lower upper points)
      (not
       (putnam-1974-b1-regular-p
        primitive lower upper points))
      (putnam-1974-b1-unit-points-p
       primitive lower upper regular-reference)
      (putnam-1974-b1-regular-p
       primitive lower upper regular-reference))
     (putnam-1974-b1-rf-positive-p
      primitive lower upper
      (putnam-1974-b1-rf-sub
       (putnam-1974-b1-rf-sum regular-reference-distances)
       (putnam-1974-b1-rf-sum point-distances)))))))

(value-triple :itpeval-statement-checked)
:q
