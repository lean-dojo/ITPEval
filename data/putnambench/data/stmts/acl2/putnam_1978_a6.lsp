;; Statement-only formalization of PutnamBench corpus artifact putnam_1978_a6:
;; fewer than 2*n^(3/2) unordered pairs among n distinct real-plane points
;; are exactly one unit apart. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; For each fixed finite configuration, its complete pattern of unit-distance
;; equalities and point-distinctness inequalities is first-order over real
;; closed fields. Hence a real counterexample exists exactly when one exists
;; over the real algebraic numbers. A single isolated algebraic number alpha
;; and rational polynomials in alpha encode every finite tuple of algebraic
;; coordinates, so this does not restrict the source's arbitrary real points.
;;
;; If m is the nonnegative number of unordered unit-distance pairs and n > 0,
;;
;;   m < 2*n^(3/2)  iff  m^2 < 4*n^3.
;;
;; The integer inequality below therefore removes the real power without
;; changing the strict bound. Rational polynomials use descending coefficient
;; order, and Sturm-Tarski queries decide equality at alpha exactly.

(defun putnam-1978-a6-rp-p (p)
  (if (consp p)
      (and (rationalp (car p))
           (putnam-1978-a6-rp-p (cdr p)))
    (equal p nil)))

(defun putnam-1978-a6-rp-normalize (p)
  (if (consp p)
      (if (equal (car p) 0)
          (putnam-1978-a6-rp-normalize (cdr p))
        p)
    nil))

(defun putnam-1978-a6-rp-neg (p)
  (if (consp p)
      (cons (- (car p))
            (putnam-1978-a6-rp-neg (cdr p)))
    nil))

(defun putnam-1978-a6-rp-add-raw (p q)
  (declare (xargs :measure (+ (acl2-count p) (acl2-count q))))
  (cond
   ((endp p) q)
   ((endp q) p)
   ((< (len p) (len q))
    (cons (car q)
          (putnam-1978-a6-rp-add-raw p (cdr q))))
   ((< (len q) (len p))
    (cons (car p)
          (putnam-1978-a6-rp-add-raw (cdr p) q)))
   (t
    (cons (+ (car p) (car q))
          (putnam-1978-a6-rp-add-raw (cdr p) (cdr q))))))

(defun putnam-1978-a6-rp-add (p q)
  (putnam-1978-a6-rp-normalize
   (putnam-1978-a6-rp-add-raw p q)))

(defun putnam-1978-a6-rp-sub (p q)
  (putnam-1978-a6-rp-add
   p (putnam-1978-a6-rp-neg q)))

(defun putnam-1978-a6-rp-scale (coefficient p)
  (if (consp p)
      (cons (* coefficient (car p))
            (putnam-1978-a6-rp-scale coefficient (cdr p)))
    nil))

(defun putnam-1978-a6-zeroes (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      nil
    (cons 0 (putnam-1978-a6-zeroes (- n 1)))))

(defun putnam-1978-a6-rp-scale-shift (coefficient p shift)
  (append
   (putnam-1978-a6-rp-scale coefficient p)
   (putnam-1978-a6-zeroes shift)))

(defun putnam-1978-a6-rp-mul-raw (p q)
  (if (consp p)
      (putnam-1978-a6-rp-add
       (putnam-1978-a6-rp-scale-shift
        (car p) q (len (cdr p)))
       (putnam-1978-a6-rp-mul-raw (cdr p) q))
    nil))

(defun putnam-1978-a6-rp-mul (p q)
  (putnam-1978-a6-rp-normalize
   (putnam-1978-a6-rp-mul-raw p q)))

(defun putnam-1978-a6-rp-square (p)
  (putnam-1978-a6-rp-mul p p))

(defun putnam-1978-a6-rp-eval-aux (p x accumulator)
  (if (consp p)
      (putnam-1978-a6-rp-eval-aux
       (cdr p) x (+ (* accumulator x) (car p)))
    accumulator))

(defun putnam-1978-a6-rp-eval (p x)
  (putnam-1978-a6-rp-eval-aux p x 0))

(defun putnam-1978-a6-rp-derivative-aux (p degree)
  (if (consp p)
      (if (zp degree)
          nil
        (cons (* degree (car p))
              (putnam-1978-a6-rp-derivative-aux
               (cdr p) (- degree 1))))
    nil))

(defun putnam-1978-a6-rp-derivative (p)
  (let ((p (putnam-1978-a6-rp-normalize p)))
    (putnam-1978-a6-rp-normalize
     (putnam-1978-a6-rp-derivative-aux
      p (nfix (- (len p) 1))))))

(defun putnam-1978-a6-rp-rem-fuel (p q fuel)
  (declare (xargs :measure (nfix fuel)))
  (let ((p (putnam-1978-a6-rp-normalize p))
        (q (putnam-1978-a6-rp-normalize q)))
    (if (or (zp fuel)
            (endp q)
            (< (len p) (len q)))
        p
      (putnam-1978-a6-rp-rem-fuel
       (putnam-1978-a6-rp-sub
        p
        (putnam-1978-a6-rp-scale-shift
         (/ (car p) (car q))
         q
         (- (len p) (len q))))
       q
       (- fuel 1)))))

(defun putnam-1978-a6-rp-rem (p q)
  (putnam-1978-a6-rp-rem-fuel
   p q (+ 1 (len (putnam-1978-a6-rp-normalize p)))))

(defun putnam-1978-a6-rp-sturm-tail (previous current fuel)
  (declare (xargs :measure (nfix fuel)))
  (let ((current (putnam-1978-a6-rp-normalize current)))
    (if (or (zp fuel) (endp current))
        nil
      (cons
       current
       (putnam-1978-a6-rp-sturm-tail
        current
        (putnam-1978-a6-rp-neg
         (putnam-1978-a6-rp-rem previous current))
        (- fuel 1))))))

(defun putnam-1978-a6-rp-sturm-sequence (p q)
  (let ((p (putnam-1978-a6-rp-normalize p))
        (q (putnam-1978-a6-rp-normalize q)))
    (if (endp p)
        nil
      (cons
       p
       (if (endp q)
           nil
         (cons
          q
          (putnam-1978-a6-rp-sturm-tail
           p q (+ 1 (len p) (len q)))))))))

(defun putnam-1978-a6-rational-sign (x)
  (cond ((< x 0) -1)
        ((< 0 x) 1)
        (t 0)))

(defun putnam-1978-a6-rp-variations-aux
    (polynomials x previous-sign)
  (if (consp polynomials)
      (let ((sign
             (putnam-1978-a6-rational-sign
              (putnam-1978-a6-rp-eval
               (car polynomials) x))))
        (if (equal sign 0)
            (putnam-1978-a6-rp-variations-aux
             (cdr polynomials) x previous-sign)
          (+ (if (and (not (equal previous-sign 0))
                      (not (equal sign previous-sign)))
                 1
               0)
             (putnam-1978-a6-rp-variations-aux
              (cdr polynomials) x sign))))
    0))

(defun putnam-1978-a6-rp-variations (polynomials x)
  (putnam-1978-a6-rp-variations-aux polynomials x 0))

(defun putnam-1978-a6-rp-cauchy-index (p q lower upper)
  (let ((sequence
         (putnam-1978-a6-rp-sturm-sequence p q)))
    (- (putnam-1978-a6-rp-variations sequence lower)
       (putnam-1978-a6-rp-variations sequence upper))))

(defun putnam-1978-a6-rp-root-count (p lower upper)
  (putnam-1978-a6-rp-cauchy-index
   p (putnam-1978-a6-rp-derivative p) lower upper))

(defun putnam-1978-a6-primitive-p (primitive lower upper)
  (and
   (putnam-1978-a6-rp-p primitive)
   (consp (putnam-1978-a6-rp-normalize primitive))
   (rationalp lower)
   (rationalp upper)
   (< lower upper)
   (not (equal
         (putnam-1978-a6-rp-eval primitive lower) 0))
   (not (equal
         (putnam-1978-a6-rp-eval primitive upper) 0))
   (equal
    (putnam-1978-a6-rp-root-count primitive lower upper)
    1)
   (not
    (equal
     (putnam-1978-a6-rp-cauchy-index
      primitive
      (putnam-1978-a6-rp-mul
       (putnam-1978-a6-rp-derivative primitive)
       (putnam-1978-a6-rp-derivative primitive))
      lower
      upper)
     0))))

(defun putnam-1978-a6-alg-sign
    (primitive lower upper value)
  (putnam-1978-a6-rp-cauchy-index
   primitive
   (putnam-1978-a6-rp-mul
    (putnam-1978-a6-rp-derivative primitive)
    value)
   lower
   upper))

(defun putnam-1978-a6-zero-at-alpha-p
    (primitive lower upper value)
  (equal
   (putnam-1978-a6-alg-sign
    primitive lower upper value)
   0))

(defun putnam-1978-a6-point-code-p (point)
  (and
   (true-listp point)
   (equal (len point) 2)
   (putnam-1978-a6-rp-p (nth 0 point))
   (putnam-1978-a6-rp-p (nth 1 point))))

(defun putnam-1978-a6-point-list-p (points)
  (if (consp points)
      (and
       (putnam-1978-a6-point-code-p (car points))
       (putnam-1978-a6-point-list-p (cdr points)))
    (equal points nil)))

(defun putnam-1978-a6-point-equal-p
    (primitive lower upper left right)
  (and
   (putnam-1978-a6-zero-at-alpha-p
    primitive lower upper
    (putnam-1978-a6-rp-sub
     (nth 0 left) (nth 0 right)))
   (putnam-1978-a6-zero-at-alpha-p
    primitive lower upper
    (putnam-1978-a6-rp-sub
     (nth 1 left) (nth 1 right)))))

(defun putnam-1978-a6-point-distinct-from-list-p
    (primitive lower upper point points)
  (if (consp points)
      (and
       (not
        (putnam-1978-a6-point-equal-p
         primitive lower upper point (car points)))
       (putnam-1978-a6-point-distinct-from-list-p
        primitive lower upper point (cdr points)))
    t))

(defun putnam-1978-a6-distinct-point-list-p
    (primitive lower upper points)
  (if (consp points)
      (and
       (putnam-1978-a6-point-distinct-from-list-p
        primitive lower upper (car points) (cdr points))
       (putnam-1978-a6-distinct-point-list-p
        primitive lower upper (cdr points)))
    t))

(defun putnam-1978-a6-distance-squared (left right)
  (putnam-1978-a6-rp-add
   (putnam-1978-a6-rp-square
    (putnam-1978-a6-rp-sub
     (nth 0 left) (nth 0 right)))
   (putnam-1978-a6-rp-square
    (putnam-1978-a6-rp-sub
     (nth 1 left) (nth 1 right)))))

(defun putnam-1978-a6-unit-distance-p
    (primitive lower upper left right)
  (putnam-1978-a6-zero-at-alpha-p
   primitive lower upper
   (putnam-1978-a6-rp-sub
    (putnam-1978-a6-distance-squared left right)
    (list 1))))

(defun putnam-1978-a6-unit-neighbor-count
    (primitive lower upper point points)
  (if (consp points)
      (+ (if
             (putnam-1978-a6-unit-distance-p
              primitive lower upper point (car points))
             1
           0)
         (putnam-1978-a6-unit-neighbor-count
          primitive lower upper point (cdr points)))
    0))

(defun putnam-1978-a6-unit-pair-count
    (primitive lower upper points)
  (if (consp points)
      (+ (putnam-1978-a6-unit-neighbor-count
          primitive lower upper (car points) (cdr points))
         (putnam-1978-a6-unit-pair-count
          primitive lower upper (cdr points)))
    0))

(defun putnambench-putnam-1978-a6-statement
    (primitive lower upper points n)
  (implies
   (and
    (putnam-1978-a6-primitive-p primitive lower upper)
    (natp n)
    (posp n)
    (true-listp points)
    (equal (len points) n)
    (putnam-1978-a6-point-list-p points)
    (putnam-1978-a6-distinct-point-list-p
     primitive lower upper points))
   (let ((unit-pairs
          (putnam-1978-a6-unit-pair-count
           primitive lower upper points)))
     (< (* unit-pairs unit-pairs)
        (* 4 (expt n 3))))))

(value-triple :itpeval-statement-checked)
:q
