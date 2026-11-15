;; Statement-only formalization of PutnamBench corpus artifact putnam_1976_b2:
;; a two-generator group with the specified orders and conjugation relation
;; has exactly eight squares, represented by 1, A^2, and B through B^6. This
;; file contains no proof.

(in-package "ACL2")

;; CARRIER, OP, and INV are ACL2 function objects. Generated predicate
;; lambdas return T outside CARRIER, so FN-EQUAL against a constant-T lambda
;; expresses universal quantification over exactly the represented group.

(defun putnam-1976-b2-quoted (object)
  (list 'quote object))

(defun putnam-1976-b2-apply1-term (function argument)
  (list 'apply$
        (putnam-1976-b2-quoted function)
        (list 'cons argument nil)))

(defun putnam-1976-b2-apply2-term (function left right)
  (list 'apply$
        (putnam-1976-b2-quoted function)
        (list 'cons left
              (list 'cons right nil))))

(defun putnam-1976-b2-carrier-term (carrier element)
  (putnam-1976-b2-apply1-term carrier element))

(defun putnam-1976-b2-operation-term (op left right)
  (putnam-1976-b2-apply2-term op left right))

(defun putnam-1976-b2-inverse-term (inv element)
  (putnam-1976-b2-apply1-term inv element))

(defun putnam-1976-b2-all-in-carrier-term
    (carrier variables)
  (if (endp variables)
      (putnam-1976-b2-quoted t)
    (list 'if
          (putnam-1976-b2-carrier-term
           carrier (car variables))
          (putnam-1976-b2-all-in-carrier-term
           carrier (cdr variables))
          (putnam-1976-b2-quoted nil))))

(defun putnam-1976-b2-restricted-predicate-term
    (carrier variables proposition)
  (list 'if
        (putnam-1976-b2-all-in-carrier-term
         carrier variables)
        proposition
        (putnam-1976-b2-quoted t)))

(defun putnam-1976-b2-and-term (left right)
  (list 'if left right (putnam-1976-b2-quoted nil)))

(defun putnam-1976-b2-true-function (formals)
  (list 'lambda formals (putnam-1976-b2-quoted t)))

(defun putnam-1976-b2-operation-closure-function (carrier op)
  (let ((op-xy
         (putnam-1976-b2-operation-term op 'x 'y)))
    (list
     'lambda
     '(x y)
     (putnam-1976-b2-restricted-predicate-term
      carrier
      '(x y)
      (putnam-1976-b2-carrier-term carrier op-xy)))))

(defun putnam-1976-b2-inverse-closure-function (carrier inv)
  (list
   'lambda
   '(x)
   (putnam-1976-b2-restricted-predicate-term
    carrier
    '(x)
    (putnam-1976-b2-carrier-term
     carrier
     (putnam-1976-b2-inverse-term inv 'x)))))

(defun putnam-1976-b2-associative-function (carrier op)
  (let* ((op-xy
          (putnam-1976-b2-operation-term op 'x 'y))
         (op-yz
          (putnam-1976-b2-operation-term op 'y 'z)))
    (list
     'lambda
     '(x y z)
     (putnam-1976-b2-restricted-predicate-term
      carrier
      '(x y z)
      (list
       'equal
       (putnam-1976-b2-operation-term op op-xy 'z)
       (putnam-1976-b2-operation-term op 'x op-yz))))))

(defun putnam-1976-b2-identity-function (carrier op one)
  (let ((left
         (list
          'equal
          (putnam-1976-b2-operation-term
           op (putnam-1976-b2-quoted one) 'x)
          'x))
        (right
         (list
          'equal
          (putnam-1976-b2-operation-term
           op 'x (putnam-1976-b2-quoted one))
          'x)))
    (list
     'lambda
     '(x)
     (putnam-1976-b2-restricted-predicate-term
      carrier
      '(x)
      (putnam-1976-b2-and-term left right)))))

(defun putnam-1976-b2-inverse-law-function
    (carrier op inv one)
  (let* ((inv-x
          (putnam-1976-b2-inverse-term inv 'x))
         (left
          (list
           'equal
           (putnam-1976-b2-operation-term op inv-x 'x)
           (putnam-1976-b2-quoted one)))
         (right
          (list
           'equal
           (putnam-1976-b2-operation-term op 'x inv-x)
           (putnam-1976-b2-quoted one))))
    (list
     'lambda
     '(x)
     (putnam-1976-b2-restricted-predicate-term
      carrier
      '(x)
      (putnam-1976-b2-and-term left right)))))

(defun putnam-1976-b2-member-p (carrier element)
  (apply$ carrier (list element)))

(defun putnam-1976-b2-multiply (op left right)
  (apply$ op (list left right)))

(defun putnam-1976-b2-power (op base exponent one)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      one
    (putnam-1976-b2-multiply
     op
     base
     (putnam-1976-b2-power op base (- exponent 1) one))))

(defun putnam-1976-b2-group-p (carrier op inv one)
  (and
   (tamep-functionp carrier)
   (tamep-functionp op)
   (tamep-functionp inv)
   (putnam-1976-b2-member-p carrier one)
   (fn-equal
    (putnam-1976-b2-operation-closure-function carrier op)
    (putnam-1976-b2-true-function '(x y)))
   (fn-equal
    (putnam-1976-b2-inverse-closure-function carrier inv)
    (putnam-1976-b2-true-function '(x)))
   (fn-equal
    (putnam-1976-b2-associative-function carrier op)
    (putnam-1976-b2-true-function '(x y z)))
   (fn-equal
    (putnam-1976-b2-identity-function carrier op one)
    (putnam-1976-b2-true-function '(x)))
   (fn-equal
    (putnam-1976-b2-inverse-law-function carrier op inv one)
    (putnam-1976-b2-true-function '(x)))))

;; A word is represented by a true list of dotted integer pairs (m . n),
;; denoting the product of the factors A^m * B^n in list order. Negative
;; powers use the supplied group inverse, exactly as in the source.

(defun putnam-1976-b2-signed-power
    (op inv base exponent one)
  (if (and (integerp exponent)
           (< exponent 0))
      (putnam-1976-b2-power
       op
       (apply$ inv (list base))
       (- exponent)
       one)
    (putnam-1976-b2-power
     op base (nfix exponent) one)))

(defun putnam-1976-b2-word-p (word)
  (if (atom word)
      (equal word nil)
    (and
     (consp (car word))
     (integerp (car (car word)))
     (integerp (cdr (car word)))
     (putnam-1976-b2-word-p (cdr word)))))

(defun putnam-1976-b2-word-value
    (op inv a b one word)
  (if (endp word)
      one
    (let* ((entry (car word))
           (a-power
            (putnam-1976-b2-signed-power
             op inv a (car entry) one))
           (b-power
            (putnam-1976-b2-signed-power
             op inv b (cdr entry) one))
           (factor
            (putnam-1976-b2-multiply
             op a-power b-power)))
      (putnam-1976-b2-multiply
       op
       factor
       (putnam-1976-b2-word-value
        op inv a b one (cdr word))))))

(defun-sk putnam-1976-b2-word-witness-exists-p
    (op inv a b one g)
  (exists (word)
    (and
     (putnam-1976-b2-word-p word)
     (equal
      g
      (putnam-1976-b2-word-value
       op inv a b one word)))))

(defun-sk putnam-1976-b2-generated-p
    (carrier op inv a b one)
  (forall (g)
    (implies
     (putnam-1976-b2-member-p carrier g)
     (putnam-1976-b2-word-witness-exists-p
      op inv a b one g))))

;; The source solution lists the words (0,0), (2,0), and (0,j) for 1 <= j <=
;; 6. Their values are exactly 1, A^2, B, ..., B^6.

(defun putnam-1976-b2-solution-elements (op a b one)
  (list
   one
   (putnam-1976-b2-power op a 2 one)
   b
   (putnam-1976-b2-power op b 2 one)
   (putnam-1976-b2-power op b 3 one)
   (putnam-1976-b2-power op b 4 one)
   (putnam-1976-b2-power op b 5 one)
   (putnam-1976-b2-power op b 6 one)))

(defun-sk putnam-1976-b2-square-p (carrier op g)
  (exists (c)
    (and
     (putnam-1976-b2-member-p carrier c)
     (equal
      (putnam-1976-b2-multiply op c c)
      g))))

(defun-sk putnam-1976-b2-exact-square-set-p
    (carrier op solution)
  (forall (g)
    (iff
     (putnam-1976-b2-square-p carrier op g)
     (member-equal g solution))))

(defun putnambench-putnam-1976-b2-statement
    (carrier op inv one a b)
  (let ((solution
          (putnam-1976-b2-solution-elements op a b one)))
    (implies
     (and
      (putnam-1976-b2-group-p carrier op inv one)
      (putnam-1976-b2-member-p carrier a)
      (putnam-1976-b2-member-p carrier b)
      (equal
       (putnam-1976-b2-power op a 4 one)
       one)
      (not
       (equal
        (putnam-1976-b2-power op a 2 one)
        one))
      (equal
       (putnam-1976-b2-power op b 7 one)
       one)
      (not (equal b one))
      (equal
       (putnam-1976-b2-multiply
        op
        (putnam-1976-b2-multiply
         op
         (putnam-1976-b2-multiply op a b)
         (apply$ inv (list a)))
        b)
       one)
      (putnam-1976-b2-generated-p
       carrier op inv a b one))
     (and
      (equal (len solution) 8)
      (no-duplicatesp-equal solution)
      (putnam-1976-b2-exact-square-set-p
       carrier op solution)))))

(value-triple :itpeval-statement-checked)
:q
