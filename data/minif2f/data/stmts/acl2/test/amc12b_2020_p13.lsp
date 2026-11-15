;; Statement-only formalization of miniF2F corpus artifact amc12b_2020_p13:
;; a principal-square-root identity involving the natural logarithms of 2,
;; 3, and 6. ACL2 represents sqrt(ln 2) and sqrt(ln 3) as positive Laurent
;; generators and extracts the three principal square roots exactly. This
;; file contains no proof.

(in-package "ACL2")

;; A term (c e2 e3) denotes
;; c * sqrt(ln 2)^e2 * sqrt(ln 3)^e3.
(defun amc12b-2020-p13-term
    (coefficient sqrt-ln2-exponent sqrt-ln3-exponent)
  (list coefficient sqrt-ln2-exponent sqrt-ln3-exponent))

(defun amc12b-2020-p13-term-coefficient (term)
  (nth 0 term))

(defun amc12b-2020-p13-term-sqrt-ln2-exponent (term)
  (nth 1 term))

(defun amc12b-2020-p13-term-sqrt-ln3-exponent (term)
  (nth 2 term))

(defun amc12b-2020-p13-term-p (term)
  (and
   (true-listp term)
   (equal (len term) 3)
   (rationalp
    (amc12b-2020-p13-term-coefficient term))
   (not
    (equal
     (amc12b-2020-p13-term-coefficient term)
     0))
   (integerp
    (amc12b-2020-p13-term-sqrt-ln2-exponent term))
   (integerp
    (amc12b-2020-p13-term-sqrt-ln3-exponent term))))

(defun amc12b-2020-p13-same-monomial-p (left right)
  (and
   (equal
    (amc12b-2020-p13-term-sqrt-ln2-exponent left)
    (amc12b-2020-p13-term-sqrt-ln2-exponent right))
   (equal
    (amc12b-2020-p13-term-sqrt-ln3-exponent left)
    (amc12b-2020-p13-term-sqrt-ln3-exponent right))))

(defun amc12b-2020-p13-monomial-before-p (left right)
  (let ((left-ln2
         (amc12b-2020-p13-term-sqrt-ln2-exponent left))
        (right-ln2
         (amc12b-2020-p13-term-sqrt-ln2-exponent right))
        (left-ln3
         (amc12b-2020-p13-term-sqrt-ln3-exponent left))
        (right-ln3
         (amc12b-2020-p13-term-sqrt-ln3-exponent right)))
    (or (< left-ln2 right-ln2)
        (and (equal left-ln2 right-ln2)
             (< left-ln3 right-ln3)))))

(defun amc12b-2020-p13-polynomial-insert (term polynomial)
  (cond
   ((equal
     (amc12b-2020-p13-term-coefficient term)
     0)
    polynomial)
   ((atom polynomial)
    (list term))
   ((amc12b-2020-p13-same-monomial-p
     term
     (car polynomial))
    (let ((coefficient
           (+
            (amc12b-2020-p13-term-coefficient term)
            (amc12b-2020-p13-term-coefficient
             (car polynomial)))))
      (if (equal coefficient 0)
          (cdr polynomial)
        (cons
         (amc12b-2020-p13-term
          coefficient
          (amc12b-2020-p13-term-sqrt-ln2-exponent term)
          (amc12b-2020-p13-term-sqrt-ln3-exponent term))
         (cdr polynomial)))))
   ((amc12b-2020-p13-monomial-before-p
     term
     (car polynomial))
    (cons term polynomial))
   (t
    (cons
     (car polynomial)
     (amc12b-2020-p13-polynomial-insert
      term
      (cdr polynomial))))))

(defun amc12b-2020-p13-polynomial-add (left right)
  (if (atom left)
      right
    (amc12b-2020-p13-polynomial-insert
     (car left)
     (amc12b-2020-p13-polynomial-add
      (cdr left)
      right))))

(defun amc12b-2020-p13-term-multiply (left right)
  (amc12b-2020-p13-term
   (*
    (amc12b-2020-p13-term-coefficient left)
    (amc12b-2020-p13-term-coefficient right))
   (+
    (amc12b-2020-p13-term-sqrt-ln2-exponent left)
    (amc12b-2020-p13-term-sqrt-ln2-exponent right))
   (+
    (amc12b-2020-p13-term-sqrt-ln3-exponent left)
    (amc12b-2020-p13-term-sqrt-ln3-exponent right))))

(defun amc12b-2020-p13-term-times-polynomial (term polynomial)
  (if (atom polynomial)
      nil
    (amc12b-2020-p13-polynomial-insert
     (amc12b-2020-p13-term-multiply
      term
      (car polynomial))
     (amc12b-2020-p13-term-times-polynomial
      term
      (cdr polynomial)))))

(defun amc12b-2020-p13-polynomial-multiply (left right)
  (if (atom left)
      nil
    (amc12b-2020-p13-polynomial-add
     (amc12b-2020-p13-term-times-polynomial
      (car left)
      right)
     (amc12b-2020-p13-polynomial-multiply
      (cdr left)
      right))))

(defun amc12b-2020-p13-monomial
    (coefficient sqrt-ln2-exponent sqrt-ln3-exponent)
  (if (equal coefficient 0)
      nil
    (list
     (amc12b-2020-p13-term
      coefficient
      sqrt-ln2-exponent
      sqrt-ln3-exponent))))

;; These are exact coordinates because ln(6) = ln(2) + ln(3), while the
;; positive generators square to ln(2) and ln(3), respectively.
(defun amc12b-2020-p13-natural-log-coordinate (n)
  (cond
   ((equal n 2)
    (amc12b-2020-p13-monomial 1 2 0))
   ((equal n 3)
    (amc12b-2020-p13-monomial 1 0 2))
   ((equal n 6)
    (amc12b-2020-p13-polynomial-add
     (amc12b-2020-p13-monomial 1 2 0)
     (amc12b-2020-p13-monomial 1 0 2)))
   (t nil)))

;; Negative Laurent exponents give the exact reciprocals of the two
;; positive, nonzero logarithms.
(defun amc12b-2020-p13-inverse-natural-log-coordinate (n)
  (cond
   ((equal n 2)
    (amc12b-2020-p13-monomial 1 -2 0))
   ((equal n 3)
    (amc12b-2020-p13-monomial 1 0 -2))
   (t nil)))

(defun amc12b-2020-p13-all-positive-terms-p (polynomial)
  (if (atom polynomial)
      t
    (and
     (amc12b-2020-p13-term-p (car polynomial))
     (< 0
        (amc12b-2020-p13-term-coefficient
         (car polynomial)))
     (amc12b-2020-p13-all-positive-terms-p
      (cdr polynomial)))))

;; Every Laurent monomial in the two positive generators is positive, so a
;; nonempty coordinate with only positive coefficients denotes a positive
;; real number.
(defun amc12b-2020-p13-positive-coordinate-p (polynomial)
  (and
   (consp polynomial)
   (amc12b-2020-p13-all-positive-terms-p polynomial)))

(defun amc12b-2020-p13-unit-monomial-root-candidate
    (radicand)
  (if
   (and
    (equal (len radicand) 1)
    (amc12b-2020-p13-term-p (car radicand))
    (equal
     (amc12b-2020-p13-term-coefficient (car radicand))
     1)
    (integerp
     (/
      (amc12b-2020-p13-term-sqrt-ln2-exponent
       (car radicand))
      2))
    (integerp
     (/
      (amc12b-2020-p13-term-sqrt-ln3-exponent
       (car radicand))
      2)))
   (amc12b-2020-p13-monomial
    1
    (/
     (amc12b-2020-p13-term-sqrt-ln2-exponent
      (car radicand))
     2)
    (/
     (amc12b-2020-p13-term-sqrt-ln3-exponent
      (car radicand))
     2))
   nil))

(defun amc12b-2020-p13-positive-binomial-root-candidate
    (radicand)
  (if
   (and
    (equal (len radicand) 3)
    (amc12b-2020-p13-term-p (car radicand))
    (amc12b-2020-p13-term-p (car (last radicand)))
    (equal
     (amc12b-2020-p13-term-coefficient
      (car radicand))
     1)
    (equal
     (amc12b-2020-p13-term-coefficient
      (car (last radicand)))
     1)
    (integerp
     (/
      (amc12b-2020-p13-term-sqrt-ln2-exponent
       (car radicand))
      2))
    (integerp
     (/
      (amc12b-2020-p13-term-sqrt-ln3-exponent
       (car radicand))
      2))
    (integerp
     (/
      (amc12b-2020-p13-term-sqrt-ln2-exponent
       (car (last radicand)))
      2))
    (integerp
     (/
      (amc12b-2020-p13-term-sqrt-ln3-exponent
       (car (last radicand)))
      2)))
   (amc12b-2020-p13-polynomial-add
    (amc12b-2020-p13-monomial
     1
     (/
      (amc12b-2020-p13-term-sqrt-ln2-exponent
       (car radicand))
      2)
     (/
      (amc12b-2020-p13-term-sqrt-ln3-exponent
       (car radicand))
      2))
    (amc12b-2020-p13-monomial
     1
     (/
      (amc12b-2020-p13-term-sqrt-ln2-exponent
       (car (last radicand)))
      2)
     (/
      (amc12b-2020-p13-term-sqrt-ln3-exponent
       (car (last radicand)))
      2)))
   nil))

;; A positive coordinate whose square is the radicand denotes its unique
;; principal real square root. The source radicands are unit-monomial or
;; positive-binomial squares, and no approximation is used.
(defun amc12b-2020-p13-principal-square-root (radicand)
  (let* ((monomial-candidate
          (amc12b-2020-p13-unit-monomial-root-candidate
           radicand))
         (candidate
          (if monomial-candidate
              monomial-candidate
            (amc12b-2020-p13-positive-binomial-root-candidate
             radicand))))
    (if
     (and
      (amc12b-2020-p13-positive-coordinate-p candidate)
      (equal
       (amc12b-2020-p13-polynomial-multiply
        candidate
        candidate)
       radicand))
     candidate
     nil)))

(defun amc12b-2020-p13-statement ()
  (let* ((ln2
          (amc12b-2020-p13-natural-log-coordinate 2))
         (ln3
          (amc12b-2020-p13-natural-log-coordinate 3))
         (ln6
          (amc12b-2020-p13-natural-log-coordinate 6))
         (inverse-ln2
          (amc12b-2020-p13-inverse-natural-log-coordinate 2))
         (inverse-ln3
          (amc12b-2020-p13-inverse-natural-log-coordinate 3))
         (left-radicand
          (amc12b-2020-p13-polynomial-add
           (amc12b-2020-p13-polynomial-multiply
            ln6
            inverse-ln2)
           (amc12b-2020-p13-polynomial-multiply
            ln6
            inverse-ln3)))
         (right-first-radicand
          (amc12b-2020-p13-polynomial-multiply
           ln3
           inverse-ln2))
         (right-second-radicand
          (amc12b-2020-p13-polynomial-multiply
           ln2
           inverse-ln3))
         (left-root
          (amc12b-2020-p13-principal-square-root
           left-radicand))
         (right-first-root
          (amc12b-2020-p13-principal-square-root
           right-first-radicand))
         (right-second-root
          (amc12b-2020-p13-principal-square-root
           right-second-radicand)))
    (and
     (consp left-root)
     (consp right-first-root)
     (consp right-second-root)
     (equal
      left-root
      (amc12b-2020-p13-polynomial-add
       right-first-root
       right-second-root)))))

(value-triple :itpeval-statement-checked)
:q
