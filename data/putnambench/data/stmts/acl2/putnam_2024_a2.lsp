;; Statement-only formalization of PutnamBench corpus artifact putnam_2024_a2:
;; the real polynomials p for which p(p(x))-x is divisible pointwise by
;; (p(x)-x)^2 are exactly p(x)=x+a and p(x)=-x+a. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The real coefficient domain is presented as a real closed ordered field.
;; The square-root and odd-degree-root laws are the standard algebraic
;; characterization of real closedness.  Polynomials are canonical nonempty
;; coefficient lists in ascending degree order.
;;
;; This is bidirectionally equivalent to the source statement: the reals form
;; such a field, while completeness of real closed fields transfers this
;; first-order polynomial assertion between any real closed field and the
;; reals. Canonical coefficient-list equality is polynomial equality because
;; every ordered field is infinite.
;;
;; ACL2 function objects supply the field operations and polynomial evaluation.
;; FN-EQUAL against a constant-T function expresses the field laws over the
;; whole represented carrier. The source's quantifiers are preserved directly:
;; DEFUN-SK existentially quantifies the polynomial q, and a second DEFUN-SK
;; universally quantifies x over the represented field in the pointwise
;; equation. No division algorithm, selected witness, or finite table replaces
;; either quantifier. The final IFF is the source set equality. The annotated
;; integer-unit slope is exactly one or negative one; canonical coefficient
;; lists therefore encode its solution polynomials as (a 1) and (a -1).

(defun putnam-2024-a2-quoted (object)
  (list 'quote object))

(defun putnam-2024-a2-apply1-term (function argument)
  (list
   'apply$
   (putnam-2024-a2-quoted function)
   (list 'cons argument nil)))

(defun putnam-2024-a2-apply2-term (function left right)
  (list
   'apply$
   (putnam-2024-a2-quoted function)
   (list 'cons left (list 'cons right nil))))

(defun putnam-2024-a2-and-term (terms)
  (if (endp terms)
      (putnam-2024-a2-quoted t)
    (list
     'if
     (car terms)
     (putnam-2024-a2-and-term (cdr terms))
     (putnam-2024-a2-quoted nil))))

(defun putnam-2024-a2-or-term (terms)
  (if (endp terms)
      (putnam-2024-a2-quoted nil)
    (list
     'if
     (car terms)
     (putnam-2024-a2-quoted t)
     (putnam-2024-a2-or-term (cdr terms)))))

(defun putnam-2024-a2-not-term (term)
  (list
   'if
   term
   (putnam-2024-a2-quoted nil)
   (putnam-2024-a2-quoted t)))

(defun putnam-2024-a2-implies-term (antecedent consequent)
  (list
   'if
   antecedent
   consequent
   (putnam-2024-a2-quoted t)))

(defun putnam-2024-a2-true-function (formals)
  (list
   'lambda
   formals
   (putnam-2024-a2-quoted t)))

(defun putnam-2024-a2-carrier-term (carrier element)
  (putnam-2024-a2-apply1-term carrier element))

(defun putnam-2024-a2-operation-term (operation left right)
  (putnam-2024-a2-apply2-term operation left right))

(defun putnam-2024-a2-all-coefficients-function (carrier)
  (list
   'lambda
   '(loop$-gvars loop$-ivars)
   (putnam-2024-a2-apply1-term carrier 'loop$-ivars)))

(defun putnam-2024-a2-all-coefficients-term
    (carrier coefficients)
  (list
   'always$+
   (putnam-2024-a2-quoted
    (putnam-2024-a2-all-coefficients-function carrier))
   (putnam-2024-a2-quoted nil)
   coefficients))

(defun putnam-2024-a2-polynomial-term
    (carrier zero coefficients)
  (putnam-2024-a2-and-term
   (list
    (list 'true-listp coefficients)
    (list 'consp coefficients)
    (putnam-2024-a2-all-coefficients-term
     carrier coefficients)
    (putnam-2024-a2-or-term
     (list
      (list 'equal
            (list 'len coefficients)
            (putnam-2024-a2-quoted 1))
      (putnam-2024-a2-not-term
       (list 'equal
             (list 'car (list 'last coefficients))
             (putnam-2024-a2-quoted zero))))))))

(defun putnam-2024-a2-field-laws-function
    (carrier zero one add mul neg inv)
  (let* ((x 'x)
         (y 'y)
         (z 'z)
         (qzero (putnam-2024-a2-quoted zero))
         (qone (putnam-2024-a2-quoted one))
         (add-xy
          (putnam-2024-a2-operation-term add x y))
         (add-yz
          (putnam-2024-a2-operation-term add y z))
         (mul-xy
          (putnam-2024-a2-operation-term mul x y))
         (mul-yz
          (putnam-2024-a2-operation-term mul y z))
         (neg-x
          (putnam-2024-a2-apply1-term neg x))
         (inv-x
          (putnam-2024-a2-apply1-term inv x))
         (domain
          (putnam-2024-a2-and-term
           (list
            (putnam-2024-a2-carrier-term carrier x)
            (putnam-2024-a2-carrier-term carrier y)
            (putnam-2024-a2-carrier-term carrier z))))
         (laws
          (putnam-2024-a2-and-term
           (list
            (putnam-2024-a2-carrier-term carrier add-xy)
            (putnam-2024-a2-carrier-term carrier mul-xy)
            (putnam-2024-a2-carrier-term carrier neg-x)
            (putnam-2024-a2-carrier-term carrier inv-x)
            (list
             'equal
             (putnam-2024-a2-operation-term add add-xy z)
             (putnam-2024-a2-operation-term add x add-yz))
            (list
             'equal
             (putnam-2024-a2-operation-term mul mul-xy z)
             (putnam-2024-a2-operation-term mul x mul-yz))
            (list
             'equal
             add-xy
             (putnam-2024-a2-operation-term add y x))
            (list
             'equal
             mul-xy
             (putnam-2024-a2-operation-term mul y x))
            (list
             'equal
             (putnam-2024-a2-operation-term add x qzero)
             x)
            (list
             'equal
             (putnam-2024-a2-operation-term add x neg-x)
             qzero)
            (list
             'equal
             (putnam-2024-a2-operation-term mul x qone)
             x)
            (putnam-2024-a2-implies-term
             (list 'equal x qzero)
             (list 'equal inv-x qzero))
            (putnam-2024-a2-implies-term
             (putnam-2024-a2-not-term
              (list 'equal x qzero))
             (list
              'equal
              (putnam-2024-a2-operation-term mul x inv-x)
              qone))
            (list
             'equal
             (putnam-2024-a2-operation-term mul x add-yz)
             (putnam-2024-a2-operation-term
              add
              (putnam-2024-a2-operation-term mul x y)
              (putnam-2024-a2-operation-term mul x z)))))))
    (list
     'lambda
     '(x y z)
     (putnam-2024-a2-implies-term domain laws))))

(defun putnam-2024-a2-order-laws-function
    (carrier zero add mul lt)
  (let* ((x 'x)
         (y 'y)
         (z 'z)
         (qzero (putnam-2024-a2-quoted zero))
         (lt-xy
          (putnam-2024-a2-operation-term lt x y))
         (lt-yx
          (putnam-2024-a2-operation-term lt y x))
         (lt-yz
          (putnam-2024-a2-operation-term lt y z))
         (lt-xz
          (putnam-2024-a2-operation-term lt x z))
         (domain
          (putnam-2024-a2-and-term
           (list
            (putnam-2024-a2-carrier-term carrier x)
            (putnam-2024-a2-carrier-term carrier y)
            (putnam-2024-a2-carrier-term carrier z))))
         (laws
          (putnam-2024-a2-and-term
           (list
            (putnam-2024-a2-not-term
             (putnam-2024-a2-operation-term lt x x))
            (putnam-2024-a2-or-term
             (list
              lt-xy
              (list 'equal x y)
              lt-yx))
            (putnam-2024-a2-implies-term
             (putnam-2024-a2-and-term
              (list lt-xy lt-yz))
             lt-xz)
            (putnam-2024-a2-implies-term
             lt-xy
             (putnam-2024-a2-operation-term
              lt
              (putnam-2024-a2-operation-term add x z)
              (putnam-2024-a2-operation-term add y z)))
            (putnam-2024-a2-implies-term
             (putnam-2024-a2-and-term
              (list
               (putnam-2024-a2-operation-term lt qzero x)
               (putnam-2024-a2-operation-term lt qzero y)))
             (putnam-2024-a2-operation-term
              lt
              qzero
              (putnam-2024-a2-operation-term mul x y)))))))
    (list
     'lambda
     '(x y z)
     (putnam-2024-a2-implies-term domain laws))))

(defun putnam-2024-a2-square-root-laws-function
    (carrier zero mul lt square-root)
  (let* ((x 'x)
         (qzero (putnam-2024-a2-quoted zero))
         (root
          (putnam-2024-a2-apply1-term square-root x))
         (domain
          (putnam-2024-a2-and-term
           (list
            (putnam-2024-a2-carrier-term carrier x)
            (putnam-2024-a2-not-term
             (putnam-2024-a2-operation-term lt x qzero)))))
         (laws
          (putnam-2024-a2-and-term
           (list
            (putnam-2024-a2-carrier-term carrier root)
            (list
             'equal
             (putnam-2024-a2-operation-term mul root root)
             x)))))
    (list
     'lambda
     '(x)
     (putnam-2024-a2-implies-term domain laws))))

(defun putnam-2024-a2-evaluation-laws-function
    (carrier zero add mul evaluate)
  (let* ((coefficient 'coefficient)
         (rest 'rest)
         (x 'x)
         (qzero (putnam-2024-a2-quoted zero))
         (domain
          (putnam-2024-a2-and-term
           (list
            (putnam-2024-a2-carrier-term
             carrier coefficient)
            (list 'true-listp rest)
            (putnam-2024-a2-all-coefficients-term
             carrier rest)
            (putnam-2024-a2-carrier-term carrier x))))
         (empty-law
          (putnam-2024-a2-implies-term
           (putnam-2024-a2-carrier-term carrier x)
           (list
            'equal
            (putnam-2024-a2-operation-term
             evaluate
             (putnam-2024-a2-quoted nil)
             x)
            qzero)))
         (recursive-value
          (putnam-2024-a2-operation-term
           add
           coefficient
           (putnam-2024-a2-operation-term
            mul
            x
            (putnam-2024-a2-operation-term
             evaluate rest x))))
         (recursive-law
          (putnam-2024-a2-implies-term
           domain
           (putnam-2024-a2-and-term
            (list
             (putnam-2024-a2-carrier-term
              carrier
              (putnam-2024-a2-operation-term
               evaluate
               (list 'cons coefficient rest)
               x))
             (list
              'equal
              (putnam-2024-a2-operation-term
               evaluate
               (list 'cons coefficient rest)
               x)
              recursive-value))))))
    (list
     'lambda
     '(coefficient rest x)
     (putnam-2024-a2-and-term
      (list empty-law recursive-law)))))

(defun putnam-2024-a2-odd-root-laws-function
    (carrier zero evaluate odd-root)
  (let* ((coefficients 'coefficients)
         (root
          (putnam-2024-a2-apply1-term
           odd-root coefficients))
         (domain
          (putnam-2024-a2-and-term
           (list
            (putnam-2024-a2-polynomial-term
             carrier zero coefficients)
            (list 'evenp (list 'len coefficients)))))
         (laws
          (putnam-2024-a2-and-term
           (list
            (putnam-2024-a2-carrier-term carrier root)
            (list
             'equal
             (putnam-2024-a2-operation-term
              evaluate coefficients root)
             (putnam-2024-a2-quoted zero))))))
    (list
     'lambda
     '(coefficients)
     (putnam-2024-a2-implies-term domain laws))))

(defun putnam-2024-a2-real-closed-field-p
    (carrier zero one add mul neg inv lt square-root odd-root
             evaluate)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp mul)
   (tamep-functionp neg)
   (tamep-functionp inv)
   (tamep-functionp lt)
   (tamep-functionp square-root)
   (tamep-functionp odd-root)
   (tamep-functionp evaluate)
   (apply$ carrier (list zero))
   (apply$ carrier (list one))
   (not (equal zero one))
   (fn-equal
    (putnam-2024-a2-field-laws-function
     carrier zero one add mul neg inv)
    (putnam-2024-a2-true-function '(x y z)))
   (fn-equal
    (putnam-2024-a2-order-laws-function
     carrier zero add mul lt)
    (putnam-2024-a2-true-function '(x y z)))
   (fn-equal
    (putnam-2024-a2-square-root-laws-function
     carrier zero mul lt square-root)
    (putnam-2024-a2-true-function '(x)))
   (fn-equal
    (putnam-2024-a2-evaluation-laws-function
     carrier zero add mul evaluate)
    (putnam-2024-a2-true-function
     '(coefficient rest x)))
   (fn-equal
    (putnam-2024-a2-odd-root-laws-function
     carrier zero evaluate odd-root)
    (putnam-2024-a2-true-function
     '(coefficients)))))

(defun putnam-2024-a2-coefficient-list-p
    (coefficients carrier)
  (if (endp coefficients)
      (equal coefficients nil)
    (and
     (apply$ carrier (list (car coefficients)))
     (putnam-2024-a2-coefficient-list-p
      (cdr coefficients) carrier))))

(defun putnam-2024-a2-polynomial-p
    (polynomial carrier zero)
  (and
   (true-listp polynomial)
   (consp polynomial)
   (putnam-2024-a2-coefficient-list-p
    polynomial carrier)
   (or
    (equal (len polynomial) 1)
    (not (equal (car (last polynomial)) zero)))))

(defun putnam-2024-a2-poly-trim (coefficients zero)
  (if (consp coefficients)
      (let ((tail
             (putnam-2024-a2-poly-trim
              (cdr coefficients) zero)))
        (if (and
             (equal (car coefficients) zero)
             (not (consp tail)))
            nil
          (cons (car coefficients) tail)))
    nil))

(defun putnam-2024-a2-poly-normalize (coefficients zero)
  (let ((trimmed
         (putnam-2024-a2-poly-trim coefficients zero)))
    (if (consp trimmed)
        trimmed
      (list zero))))

(defun putnam-2024-a2-poly-zero-p (polynomial zero)
  (equal
   (putnam-2024-a2-poly-normalize polynomial zero)
   (list zero)))

(defun putnam-2024-a2-poly-add-raw (left right add)
  (cond
   ((consp left)
    (if (consp right)
        (cons
         (apply$ add (list (car left) (car right)))
         (putnam-2024-a2-poly-add-raw
          (cdr left) (cdr right) add))
      left))
   (t right)))

(defun putnam-2024-a2-poly-add (left right zero add)
  (putnam-2024-a2-poly-normalize
   (putnam-2024-a2-poly-add-raw left right add)
   zero))

(defun putnam-2024-a2-poly-scale-raw
    (scalar polynomial mul)
  (if (consp polynomial)
      (cons
       (apply$ mul (list scalar (car polynomial)))
       (putnam-2024-a2-poly-scale-raw
        scalar (cdr polynomial) mul))
    nil))

(defun putnam-2024-a2-poly-negate-raw (polynomial neg)
  (if (consp polynomial)
      (cons
       (apply$ neg (list (car polynomial)))
       (putnam-2024-a2-poly-negate-raw
        (cdr polynomial) neg))
    nil))

(defun putnam-2024-a2-poly-subtract
    (left right zero add neg)
  (putnam-2024-a2-poly-add
   left
   (putnam-2024-a2-poly-negate-raw right neg)
   zero
   add))

(defun putnam-2024-a2-poly-multiply-raw
    (left right zero add mul)
  (if (consp left)
      (putnam-2024-a2-poly-add-raw
       (putnam-2024-a2-poly-scale-raw
        (car left) right mul)
       (cons
        zero
        (putnam-2024-a2-poly-multiply-raw
         (cdr left) right zero add mul))
       add)
    nil))

(defun putnam-2024-a2-poly-multiply
    (left right zero add mul)
  (putnam-2024-a2-poly-normalize
   (putnam-2024-a2-poly-multiply-raw
    left right zero add mul)
   zero))

(defun putnam-2024-a2-poly-compose-raw
    (outer inner zero add mul)
  (if (consp outer)
      (putnam-2024-a2-poly-add-raw
       (list (car outer))
       (putnam-2024-a2-poly-multiply-raw
        inner
        (putnam-2024-a2-poly-compose-raw
         (cdr outer) inner zero add mul)
        zero
        add
        mul)
       add)
    nil))

(defun putnam-2024-a2-poly-compose
    (outer inner zero add mul)
  (putnam-2024-a2-poly-normalize
   (putnam-2024-a2-poly-compose-raw
    outer inner zero add mul)
   zero))

(defun putnam-2024-a2-zero-list (count zero)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons
     zero
     (putnam-2024-a2-zero-list (- count 1) zero))))

(defun putnam-2024-a2-poly-monomial
    (coefficient degree zero)
  (putnam-2024-a2-poly-normalize
   (append
    (putnam-2024-a2-zero-list degree zero)
    (list coefficient))
   zero))

(defun putnam-2024-a2-poly-leading-coefficient
    (polynomial zero)
  (car
   (last
    (putnam-2024-a2-poly-normalize polynomial zero))))

(defun putnam-2024-a2-poly-divmod-steps
    (remainder divisor quotient zero add mul neg inv steps)
  (declare (xargs :measure (nfix steps)))
  (let* ((normalized-remainder
          (putnam-2024-a2-poly-normalize remainder zero))
         (normalized-divisor
          (putnam-2024-a2-poly-normalize divisor zero))
         (normalized-quotient
          (putnam-2024-a2-poly-normalize quotient zero)))
    (if (or
         (zp steps)
         (putnam-2024-a2-poly-zero-p
          normalized-remainder zero)
         (putnam-2024-a2-poly-zero-p
          normalized-divisor zero)
         (< (len normalized-remainder)
            (len normalized-divisor)))
        (cons normalized-quotient normalized-remainder)
      (let* ((degree-difference
              (- (len normalized-remainder)
                 (len normalized-divisor)))
             (coefficient
              (apply$
               mul
               (list
                (putnam-2024-a2-poly-leading-coefficient
                 normalized-remainder zero)
                (apply$
                 inv
                 (list
                  (putnam-2024-a2-poly-leading-coefficient
                   normalized-divisor zero))))))
             (term
              (putnam-2024-a2-poly-monomial
               coefficient degree-difference zero)))
        (putnam-2024-a2-poly-divmod-steps
         (putnam-2024-a2-poly-subtract
          normalized-remainder
          (putnam-2024-a2-poly-multiply
           term normalized-divisor zero add mul)
          zero
          add
          neg)
         normalized-divisor
         (putnam-2024-a2-poly-add
          normalized-quotient term zero add)
         zero
         add
         mul
         neg
         inv
         (- steps 1))))))

(defun putnam-2024-a2-poly-divmod
    (dividend divisor zero add mul neg inv)
  (putnam-2024-a2-poly-divmod-steps
   dividend
   divisor
   (list zero)
   zero
   add
   mul
   neg
   inv
   (+ 1
      (len
       (putnam-2024-a2-poly-normalize
        dividend zero)))))

(defun-sk putnam-2024-a2-pointwise-identity-p
    (carrier add mul neg evaluate polynomial quotient)
  (forall (x)
    (implies
     (apply$ carrier (list x))
     (let* ((p-of-x
             (apply$ evaluate (list polynomial x)))
            (p-of-p-of-x
             (apply$ evaluate (list polynomial p-of-x)))
            (q-of-x
             (apply$ evaluate (list quotient x)))
            (p-minus-x
             (apply$
              add
              (list p-of-x (apply$ neg (list x)))))
            (left
             (apply$
              add
              (list p-of-p-of-x (apply$ neg (list x)))))
            (right
             (apply$
              mul
              (list
               (apply$ mul (list p-minus-x p-minus-x))
               q-of-x))))
       (equal left right)))))

(defun-sk putnam-2024-a2-q-exists-p
    (carrier zero add mul neg evaluate polynomial)
  (exists (quotient)
    (and
     (putnam-2024-a2-polynomial-p quotient carrier zero)
     (putnam-2024-a2-pointwise-identity-p
      carrier add mul neg evaluate polynomial quotient))))

(defun putnam-2024-a2-solution-p
    (polynomial one neg)
  (and
   (equal (len polynomial) 2)
   (or
    (equal (cadr polynomial) one)
    (equal
     (cadr polynomial)
     (apply$ neg (list one))))))

(defun putnambench-putnam-2024-a2-statement
    (carrier zero one add mul neg inv lt square-root odd-root
             evaluate polynomial)
  (implies
   (and
    (putnam-2024-a2-real-closed-field-p
     carrier zero one add mul neg inv lt square-root odd-root
     evaluate)
    (putnam-2024-a2-polynomial-p
     polynomial carrier zero))
   (iff
    (putnam-2024-a2-q-exists-p
     carrier zero add mul neg evaluate polynomial)
    (putnam-2024-a2-solution-p
     polynomial one neg))))

(value-triple :itpeval-statement-checked)
:q
