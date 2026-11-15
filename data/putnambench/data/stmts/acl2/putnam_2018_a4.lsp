;; Statement-only formalization of PutnamBench corpus artifact putnam_2018_a4:
;; a coprime floor-difference word in two elements of an arbitrary group,
;; when equal to the identity, forces the two elements to commute. This file
;; contains no proof.

(in-package "ACL2")

;; CARRIER, OP, and INV are ACL2 function objects. The generated predicate
;; lambdas return T outside CARRIER, so FN-EQUAL with a constant-T lambda
;; expresses each group law universally on the represented type.

(defun putnam-2018-a4-quoted (object)
  (list 'quote object))

(defun putnam-2018-a4-apply1-term (function argument)
  (list 'apply$
        (putnam-2018-a4-quoted function)
        (list 'cons argument nil)))

(defun putnam-2018-a4-apply2-term (function left right)
  (list 'apply$
        (putnam-2018-a4-quoted function)
        (list 'cons left
              (list 'cons right nil))))

(defun putnam-2018-a4-carrier-term (carrier element)
  (putnam-2018-a4-apply1-term carrier element))

(defun putnam-2018-a4-operation-term (op left right)
  (putnam-2018-a4-apply2-term op left right))

(defun putnam-2018-a4-inverse-term (inv element)
  (putnam-2018-a4-apply1-term inv element))

(defun putnam-2018-a4-all-in-carrier-term
    (carrier variables)
  (if (endp variables)
      (putnam-2018-a4-quoted t)
    (list 'if
          (putnam-2018-a4-carrier-term
           carrier (car variables))
          (putnam-2018-a4-all-in-carrier-term
           carrier (cdr variables))
          (putnam-2018-a4-quoted nil))))

(defun putnam-2018-a4-restricted-predicate-term
    (carrier variables proposition)
  (list 'if
        (putnam-2018-a4-all-in-carrier-term
         carrier variables)
        proposition
        (putnam-2018-a4-quoted t)))

(defun putnam-2018-a4-and-term (left right)
  (list 'if left right (putnam-2018-a4-quoted nil)))

(defun putnam-2018-a4-true-function (formals)
  (list 'lambda formals (putnam-2018-a4-quoted t)))

(defun putnam-2018-a4-operation-closure-function (carrier op)
  (let ((op-xy
         (putnam-2018-a4-operation-term op 'x 'y)))
    (list
     'lambda
     '(x y)
     (putnam-2018-a4-restricted-predicate-term
      carrier
      '(x y)
      (putnam-2018-a4-carrier-term carrier op-xy)))))

(defun putnam-2018-a4-inverse-closure-function (carrier inv)
  (list
   'lambda
   '(x)
   (putnam-2018-a4-restricted-predicate-term
    carrier
    '(x)
    (putnam-2018-a4-carrier-term
     carrier
     (putnam-2018-a4-inverse-term inv 'x)))))

(defun putnam-2018-a4-associative-function (carrier op)
  (let* ((op-xy
          (putnam-2018-a4-operation-term op 'x 'y))
         (op-yz
          (putnam-2018-a4-operation-term op 'y 'z)))
    (list
     'lambda
     '(x y z)
     (putnam-2018-a4-restricted-predicate-term
      carrier
      '(x y z)
      (list
       'equal
       (putnam-2018-a4-operation-term op op-xy 'z)
       (putnam-2018-a4-operation-term op 'x op-yz))))))

(defun putnam-2018-a4-identity-function (carrier op one)
  (let ((left
         (list
          'equal
          (putnam-2018-a4-operation-term
           op (putnam-2018-a4-quoted one) 'x)
          'x))
        (right
         (list
          'equal
          (putnam-2018-a4-operation-term
           op 'x (putnam-2018-a4-quoted one))
          'x)))
    (list
     'lambda
     '(x)
     (putnam-2018-a4-restricted-predicate-term
      carrier
      '(x)
      (putnam-2018-a4-and-term left right)))))

(defun putnam-2018-a4-inverse-law-function
    (carrier op inv one)
  (let* ((inv-x
          (putnam-2018-a4-inverse-term inv 'x))
         (left
          (list
           'equal
           (putnam-2018-a4-operation-term op inv-x 'x)
           (putnam-2018-a4-quoted one)))
         (right
          (list
           'equal
           (putnam-2018-a4-operation-term op 'x inv-x)
           (putnam-2018-a4-quoted one))))
    (list
     'lambda
     '(x)
     (putnam-2018-a4-restricted-predicate-term
      carrier
      '(x)
      (putnam-2018-a4-and-term left right)))))

(defun putnam-2018-a4-member-p (carrier element)
  (apply$ carrier (list element)))

(defun putnam-2018-a4-multiply (op left right)
  (apply$ op (list left right)))

(defun putnam-2018-a4-group-p (carrier op inv one)
  (and
   (tamep-functionp carrier)
   (tamep-functionp op)
   (tamep-functionp inv)
   (putnam-2018-a4-member-p carrier one)
   (fn-equal
    (putnam-2018-a4-operation-closure-function carrier op)
    (putnam-2018-a4-true-function '(x y)))
   (fn-equal
    (putnam-2018-a4-inverse-closure-function carrier inv)
    (putnam-2018-a4-true-function '(x)))
   (fn-equal
    (putnam-2018-a4-associative-function carrier op)
    (putnam-2018-a4-true-function '(x y z)))
   (fn-equal
    (putnam-2018-a4-identity-function carrier op one)
    (putnam-2018-a4-true-function '(x)))
   (fn-equal
    (putnam-2018-a4-inverse-law-function carrier op inv one)
    (putnam-2018-a4-true-function '(x)))))

;; For positive M and N, the real floor difference in the source is exactly
;; this integer quotient difference and is always a natural number.
(defun putnam-2018-a4-exponent (m n k)
  (- (floor (* m k) n)
     (floor (* m (- k 1)) n)))

(defun putnam-2018-a4-power (op base exponent one)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      one
    (putnam-2018-a4-multiply
     op
     (putnam-2018-a4-power
      op base (- exponent 1) one)
     base)))

;; This is the source recursion P_0=1 and
;; P_k=((P_(k-1)*g)*h^(a_k)) for k=1,...,n.
(defun putnam-2018-a4-product-prefix
    (op one g h m n k)
  (declare (xargs :measure (nfix k)))
  (if (zp k)
      one
    (putnam-2018-a4-multiply
     op
     (putnam-2018-a4-multiply
      op
      (putnam-2018-a4-product-prefix
       op one g h m n (- k 1))
      g)
     (putnam-2018-a4-power
      op h
      (putnam-2018-a4-exponent m n k)
      one))))

;; Searching all possible common divisors from M down to 2 is equivalent to
;; gcd(M,N)=1 when M and N are positive.
(defun putnam-2018-a4-coprime-through-p
    (m n divisor)
  (declare (xargs :measure (nfix divisor)))
  (if (and (natp divisor)
           (< 1 divisor))
      (and
       (not
        (and
         (equal (mod m divisor) 0)
         (equal (mod n divisor) 0)))
       (putnam-2018-a4-coprime-through-p
        m n (- divisor 1)))
    t))

(defun putnam-2018-a4-coprime-p (m n)
  (and
   (posp m)
   (posp n)
   (putnam-2018-a4-coprime-through-p m n m)))

(defun putnambench-putnam-2018-a4-statement
    (m n carrier op inv one g h)
  (implies
   (and
    (putnam-2018-a4-coprime-p m n)
    (putnam-2018-a4-group-p carrier op inv one)
    (putnam-2018-a4-member-p carrier g)
    (putnam-2018-a4-member-p carrier h)
    (equal
     (putnam-2018-a4-product-prefix
      op one g h m n n)
     one))
   (equal
    (putnam-2018-a4-multiply op g h)
    (putnam-2018-a4-multiply op h g))))

(value-triple :itpeval-statement-checked)
:q
