;; Statement-only formalization of PutnamBench corpus artifact putnam_1978_a4:
;; consequences of the bypass identity (a*b)*(c*d) = a*d and the existence
;; of a finite idempotent bypass algebra with two specified nontrivial
;; multiplication behaviors. This file contains no proof.

(in-package "ACL2")

;; For the universal part, DEFSTUB supplies an arbitrary carrier predicate and
;; binary operation conservatively. The existential finite algebra below is
;; represented separately by concrete finite data.

(defstub putnam-1978-a4-carrier (x) t)
(defstub putnam-1978-a4-operation (x y) t)

(defun putnam-1978-a4-quoted (object)
  (list 'quote object))

(defun putnam-1978-a4-apply1-term (function argument)
  (list 'apply$
        (putnam-1978-a4-quoted function)
        (list 'cons argument nil)))

(defun putnam-1978-a4-apply2-term (function left right)
  (list 'apply$
        (putnam-1978-a4-quoted function)
        (list 'cons left
              (list 'cons right nil))))

(defun putnam-1978-a4-carrier-term (carrier element)
  (putnam-1978-a4-apply1-term carrier element))

(defun putnam-1978-a4-operation-term (op left right)
  (putnam-1978-a4-apply2-term op left right))

(defun putnam-1978-a4-all-in-carrier-term
    (carrier variables)
  (if (endp variables)
      (putnam-1978-a4-quoted t)
    (list 'if
          (putnam-1978-a4-carrier-term
           carrier (car variables))
          (putnam-1978-a4-all-in-carrier-term
           carrier (cdr variables))
          (putnam-1978-a4-quoted nil))))

(defun putnam-1978-a4-restricted-predicate-term
    (carrier variables proposition)
  (list 'if
        (putnam-1978-a4-all-in-carrier-term
         carrier variables)
        proposition
        (putnam-1978-a4-quoted t)))

(defun putnam-1978-a4-true-function (formals)
  (list 'lambda formals (putnam-1978-a4-quoted t)))

(defun putnam-1978-a4-operation-closure-function
    (carrier op)
  (list
   'lambda
   '(a b)
   (putnam-1978-a4-restricted-predicate-term
    carrier
    '(a b)
    (putnam-1978-a4-carrier-term
     carrier
     (putnam-1978-a4-operation-term op 'a 'b)))))

(defun putnam-1978-a4-bypass-function (carrier op)
  (let* ((op-ab
          (putnam-1978-a4-operation-term op 'a 'b))
         (op-cd
          (putnam-1978-a4-operation-term op 'c 'd)))
    (list
     'lambda
     '(a b c d)
     (putnam-1978-a4-restricted-predicate-term
      carrier
      '(a b c d)
      (list
       'equal
       (putnam-1978-a4-operation-term op op-ab op-cd)
       (putnam-1978-a4-operation-term op 'a 'd))))))

(defun putnam-1978-a4-member-p (element)
  (if (putnam-1978-a4-carrier element) t nil))

(defun putnam-1978-a4-multiply (left right)
  (putnam-1978-a4-operation left right))

(defun-sk putnam-1978-a4-operation-closed-p ()
  (forall (a b)
    (implies
     (and
      (putnam-1978-a4-member-p a)
      (putnam-1978-a4-member-p b))
     (putnam-1978-a4-member-p
      (putnam-1978-a4-multiply a b)))))

(defun-sk putnam-1978-a4-bypass-p ()
  (forall (a b c d)
    (implies
     (and
      (putnam-1978-a4-member-p a)
      (putnam-1978-a4-member-p b)
      (putnam-1978-a4-member-p c)
      (putnam-1978-a4-member-p d))
     (equal
      (putnam-1978-a4-multiply
       (putnam-1978-a4-multiply a b)
       (putnam-1978-a4-multiply c d))
      (putnam-1978-a4-multiply a d)))))

(defun putnam-1978-a4-algebra-p ()
  (and
   (putnam-1978-a4-operation-closed-p)
   (putnam-1978-a4-bypass-p)))

;; The existential finite algebra is represented by
;;
;;   (carrier pairs quadruples operation-table).
;;
;; CARRIER is a duplicate-free nonempty list. PAIRS and QUADRUPLES are
;; duplicate-free complete enumerations, certified by membership and the
;; cardinalities |S|^2 and |S|^4. OPERATION-TABLE has one closed value for
;; every ordered pair. Thus this data is definitionally equivalent, up to
;; enumeration order, to a finite type with a binary operation.
;;
;; ALWAYS$ and THEREIS$ retain the finite inner universal and existential
;; conditions. The final DEFUN-SK below explicitly quantifies the complete
;; finite-algebra witness; function extensionality is not used as a surrogate
;; for that existential quantifier.

;; The following helpers construct tame lambda terms. They run while building
;; the existential predicate and are not themselves called through APPLY$.

(defun putnam-1978-a4-expression-list (expressions)
  (if (endp expressions)
      (putnam-1978-a4-quoted nil)
    (list 'cons
          (car expressions)
          (putnam-1978-a4-expression-list
           (cdr expressions)))))

(defun putnam-1978-a4-data-call-expression
    (function argument-expressions)
  (putnam-1978-a4-expression-list
   (cons (putnam-1978-a4-quoted function)
         argument-expressions)))

(defun putnam-1978-a4-runtime-quote-expression (value-term)
  (putnam-1978-a4-expression-list
   (list (putnam-1978-a4-quoted 'quote)
         value-term)))

(defun putnam-1978-a4-dynamic-lambda-expression
    (formals body-term-expression)
  (putnam-1978-a4-expression-list
   (list (putnam-1978-a4-quoted 'lambda)
         (putnam-1978-a4-quoted formals)
         body-term-expression)))

(defun putnam-1978-a4-data-if-expression
    (test-expression then-expression else-expression)
  (putnam-1978-a4-data-call-expression
   'if
   (list test-expression then-expression else-expression)))

(defun putnam-1978-a4-data-and-expression (expressions)
  (if (endp expressions)
      (putnam-1978-a4-quoted '(quote t))
    (putnam-1978-a4-data-if-expression
     (car expressions)
     (putnam-1978-a4-data-and-expression
      (cdr expressions))
     (putnam-1978-a4-quoted '(quote nil)))))

(defun putnam-1978-a4-and-term (terms)
  (if (endp terms)
      (putnam-1978-a4-quoted t)
    (list 'if
          (car terms)
          (putnam-1978-a4-and-term (cdr terms))
          (putnam-1978-a4-quoted nil))))

(defun putnam-1978-a4-not-term (term)
  (list 'if
        term
        (putnam-1978-a4-quoted nil)
        (putnam-1978-a4-quoted t)))

(defun putnam-1978-a4-table-operation-expression
    (table-value-term left-term-expression right-term-expression)
  (let* ((nil-term-expression
          (putnam-1978-a4-quoted '(quote nil)))
         (tail-expression
          (putnam-1978-a4-data-call-expression
           'cons
           (list right-term-expression nil-term-expression)))
         (key-expression
          (putnam-1978-a4-data-call-expression
           'cons
           (list left-term-expression tail-expression)))
         (association-expression
          (putnam-1978-a4-data-call-expression
           'assoc-equal
           (list
            key-expression
            (putnam-1978-a4-runtime-quote-expression
             table-value-term)))))
    (putnam-1978-a4-data-call-expression
     'cdr
     (list association-expression))))

(defun putnam-1978-a4-member-expression
    (carrier-value-term element-term-expression)
  (putnam-1978-a4-data-call-expression
   'member-equal
   (list
    element-term-expression
    (putnam-1978-a4-runtime-quote-expression
     carrier-value-term))))

(defun putnam-1978-a4-valid-pair-function-expression
    (carrier-value-term formal)
  (let* ((first
          (putnam-1978-a4-quoted
           (list 'car formal)))
         (second
          (putnam-1978-a4-quoted
           (list 'car (list 'cdr formal))))
         (body
          (putnam-1978-a4-data-and-expression
           (list
            (putnam-1978-a4-quoted
             (list 'true-listp formal))
            (putnam-1978-a4-quoted
             (list 'equal (list 'len formal) 2))
            (putnam-1978-a4-member-expression
             carrier-value-term first)
            (putnam-1978-a4-member-expression
             carrier-value-term second)))))
    (putnam-1978-a4-dynamic-lambda-expression
     (list formal) body)))

(defun putnam-1978-a4-valid-quadruple-function-expression
    (carrier-value-term)
  (let* ((first
          (putnam-1978-a4-quoted '(car quadruple)))
         (second
          (putnam-1978-a4-quoted
           '(car (cdr quadruple))))
         (third
          (putnam-1978-a4-quoted
           '(car (cdr (cdr quadruple)))))
         (fourth
          (putnam-1978-a4-quoted
           '(car (cdr (cdr (cdr quadruple))))))
         (body
          (putnam-1978-a4-data-and-expression
           (list
            (putnam-1978-a4-quoted
             '(true-listp quadruple))
            (putnam-1978-a4-quoted
             '(equal (len quadruple) 4))
            (putnam-1978-a4-member-expression
             carrier-value-term first)
            (putnam-1978-a4-member-expression
             carrier-value-term second)
            (putnam-1978-a4-member-expression
             carrier-value-term third)
            (putnam-1978-a4-member-expression
             carrier-value-term fourth)))))
    (putnam-1978-a4-dynamic-lambda-expression
     '(quadruple) body)))

(defun putnam-1978-a4-valid-table-entry-function-expression
    (carrier-value-term)
  (let* ((key
          (putnam-1978-a4-quoted '(car entry)))
         (first
          (putnam-1978-a4-quoted
           '(car (car entry))))
         (second
          (putnam-1978-a4-quoted
           '(car (cdr (car entry)))))
         (value
          (putnam-1978-a4-quoted '(cdr entry)))
         (body
          (putnam-1978-a4-data-and-expression
           (list
            (putnam-1978-a4-quoted '(consp entry))
            (putnam-1978-a4-data-call-expression
             'true-listp (list key))
            (putnam-1978-a4-data-call-expression
             'equal
             (list
              (putnam-1978-a4-data-call-expression
               'len (list key))
              (putnam-1978-a4-quoted 2)))
            (putnam-1978-a4-member-expression
             carrier-value-term first)
            (putnam-1978-a4-member-expression
             carrier-value-term second)
            (putnam-1978-a4-member-expression
             carrier-value-term value)))))
    (putnam-1978-a4-dynamic-lambda-expression
     '(entry) body)))

(defun putnam-1978-a4-idempotent-function-expression
    (table-value-term)
  (let* ((element
          (putnam-1978-a4-quoted 'element))
         (product
          (putnam-1978-a4-table-operation-expression
           table-value-term element element))
         (body
          (putnam-1978-a4-data-call-expression
           'equal
           (list product element))))
    (putnam-1978-a4-dynamic-lambda-expression
     '(element) body)))

(defun putnam-1978-a4-bypass-table-function-expression
    (table-value-term)
  (let* ((a
          (putnam-1978-a4-quoted '(car quadruple)))
         (b
          (putnam-1978-a4-quoted
           '(car (cdr quadruple))))
         (c
          (putnam-1978-a4-quoted
           '(car (cdr (cdr quadruple)))))
         (d
          (putnam-1978-a4-quoted
           '(car (cdr (cdr (cdr quadruple))))))
         (ab
          (putnam-1978-a4-table-operation-expression
           table-value-term a b))
         (cd
          (putnam-1978-a4-table-operation-expression
           table-value-term c d))
         (left
          (putnam-1978-a4-table-operation-expression
           table-value-term ab cd))
         (right
          (putnam-1978-a4-table-operation-expression
           table-value-term a d))
         (body
          (putnam-1978-a4-data-call-expression
           'equal
           (list left right))))
    (putnam-1978-a4-dynamic-lambda-expression
     '(quadruple) body)))

(defun putnam-1978-a4-left-projection-witness-function-expression
    (table-value-term)
  (let* ((a
          (putnam-1978-a4-quoted '(car pair)))
         (b
          (putnam-1978-a4-quoted
           '(car (cdr pair))))
         (product
          (putnam-1978-a4-table-operation-expression
           table-value-term a b))
         (body
          (putnam-1978-a4-data-and-expression
           (list
            (putnam-1978-a4-data-call-expression
             'equal (list product a))
            (putnam-1978-a4-data-if-expression
             (putnam-1978-a4-data-call-expression
              'equal (list a b))
             (putnam-1978-a4-quoted '(quote nil))
             (putnam-1978-a4-quoted '(quote t)))))))
    (putnam-1978-a4-dynamic-lambda-expression
     '(pair) body)))

(defun putnam-1978-a4-non-left-projection-function-expression
    (table-value-term)
  (let* ((a
          (putnam-1978-a4-quoted '(car pair)))
         (b
          (putnam-1978-a4-quoted
           '(car (cdr pair))))
         (product
          (putnam-1978-a4-table-operation-expression
           table-value-term a b))
         (body
          (putnam-1978-a4-data-if-expression
           (putnam-1978-a4-data-call-expression
            'equal (list product a))
           (putnam-1978-a4-quoted '(quote nil))
           (putnam-1978-a4-quoted '(quote t)))))
    (putnam-1978-a4-dynamic-lambda-expression
     '(pair) body)))

(defun putnam-1978-a4-finite-witness-failure-function ()
  (let* ((carrier '(car witness))
         (pairs '(car (cdr witness)))
         (quadruples '(car (cdr (cdr witness))))
         (table '(car (cdr (cdr (cdr witness)))))
         (carrier-size '(len (car witness)))
         (pair-count
          (list 'binary-* carrier-size carrier-size))
         (valid-pair-function
          (putnam-1978-a4-quoted
           '(lambda (loop$-gvars loop$-ivars)
              (if (true-listp loop$-ivars)
                  (if (equal (len loop$-ivars) '2)
                      (if (member-equal
                           (car loop$-ivars)
                           (car loop$-gvars))
                          (if (member-equal
                               (car (cdr loop$-ivars))
                               (car loop$-gvars))
                              't
                            'nil)
                        'nil)
                    'nil)
                'nil))))
         (valid-quadruple-function
          (putnam-1978-a4-quoted
           '(lambda (loop$-gvars loop$-ivars)
              (if (true-listp loop$-ivars)
                  (if (equal (len loop$-ivars) '4)
                      (if (member-equal
                           (car loop$-ivars)
                           (car loop$-gvars))
                          (if (member-equal
                               (car (cdr loop$-ivars))
                               (car loop$-gvars))
                              (if (member-equal
                                   (car (cdr (cdr loop$-ivars)))
                                   (car loop$-gvars))
                                  (if (member-equal
                                       (car (cdr (cdr (cdr loop$-ivars))))
                                       (car loop$-gvars))
                                      't
                                    'nil)
                                'nil)
                            'nil)
                        'nil)
                    'nil)
                'nil))))
         (valid-table-entry-function
          (putnam-1978-a4-quoted
           '(lambda (loop$-gvars loop$-ivars)
              (if (true-listp loop$-ivars)
                  (if (equal (len loop$-ivars) '2)
                      (if (true-listp (car loop$-ivars))
                          (if (equal (len (car loop$-ivars)) '2)
                              (if (member-equal
                                   (car (car loop$-ivars))
                                   (car loop$-gvars))
                                  (if (member-equal
                                       (car (cdr (car loop$-ivars)))
                                       (car loop$-gvars))
                                      (if (member-equal
                                           (car (cdr loop$-ivars))
                                           (car loop$-gvars))
                                          't
                                        'nil)
                                    'nil)
                                'nil)
                            'nil)
                        'nil)
                    'nil)
                'nil))))
         (idempotent-function
          (putnam-1978-a4-quoted
           '(lambda (loop$-gvars loop$-ivars)
              (if (equal (car loop$-ivars)
                         (car (cdr loop$-ivars)))
                  (equal
                   (car
                    (cdr
                     (assoc-equal
                      (cons (car loop$-ivars)
                            (cons (car (cdr loop$-ivars)) 'nil))
                      (car loop$-gvars))))
                   (car loop$-ivars))
                't))))
         (bypass-function
          (putnam-1978-a4-quoted
           '(lambda (loop$-gvars loop$-ivars)
              (equal
               (car
                (cdr
                 (assoc-equal
                  (cons
                   (car
                    (cdr
                     (assoc-equal
                      (cons (car loop$-ivars)
                            (cons (car (cdr loop$-ivars)) 'nil))
                      (car loop$-gvars))))
                   (cons
                    (car
                     (cdr
                      (assoc-equal
                       (cons (car (cdr (cdr loop$-ivars)))
                             (cons
                              (car (cdr (cdr (cdr loop$-ivars))))
                              'nil))
                       (car loop$-gvars))))
                    'nil))
                  (car loop$-gvars))))
               (car
                (cdr
                 (assoc-equal
                  (cons (car loop$-ivars)
                        (cons
                         (car (cdr (cdr (cdr loop$-ivars))))
                         'nil))
                  (car loop$-gvars))))))))
         (left-projection-witness-function
          (putnam-1978-a4-quoted
           '(lambda (loop$-gvars loop$-ivars)
              (if (equal
                   (car
                    (cdr
                     (assoc-equal
                      (cons (car loop$-ivars)
                            (cons (car (cdr loop$-ivars)) 'nil))
                      (car loop$-gvars))))
                   (car loop$-ivars))
                  (if (equal (car loop$-ivars)
                             (car (cdr loop$-ivars)))
                      'nil
                    't)
                'nil))))
         (non-left-projection-function
          (putnam-1978-a4-quoted
           '(lambda (loop$-gvars loop$-ivars)
              (if (equal
                   (car
                    (cdr
                     (assoc-equal
                      (cons (car loop$-ivars)
                            (cons (car (cdr loop$-ivars)) 'nil))
                      (car loop$-gvars))))
                   (car loop$-ivars))
                  'nil
                't))))
         (qualification
          (putnam-1978-a4-and-term
           (list
            '(true-listp witness)
            '(equal (len witness) '4)
            '(true-listp (car witness))
            '(consp (car witness))
            '(no-duplicatesp-equal (car witness))
            '(true-listp (car (cdr witness)))
            '(no-duplicatesp-equal (car (cdr witness)))
            (list
             'equal
             (list 'len pairs)
             pair-count)
            (list
             'always$+
             valid-pair-function
             (list 'cons carrier nil)
             pairs)
            '(true-listp (car (cdr (cdr witness))))
            '(no-duplicatesp-equal
              (car (cdr (cdr witness))))
            (list
             'equal
             (list 'len quadruples)
             (list 'binary-* pair-count pair-count))
            (list
             'always$+
             valid-quadruple-function
             (list 'cons carrier nil)
             quadruples)
            '(true-listp (car (cdr (cdr (cdr witness)))))
            '(alistp (car (cdr (cdr (cdr witness)))))
            (list
             'equal
             (list 'len table)
             pair-count)
            (list
             'no-duplicatesp-equal
             (list 'strip-cars table))
            (list
             'always$+
             valid-table-entry-function
             (list 'cons carrier nil)
             table)
            (list
             'always$+
             idempotent-function
             (list 'cons table nil)
             pairs)
            (list
             'always$+
             bypass-function
             (list 'cons table nil)
             quadruples)
            (list
             'thereis$+
             left-projection-witness-function
             (list 'cons table nil)
             pairs)
            (list
             'thereis$+
             non-left-projection-function
             (list 'cons table nil)
             pairs)))))
    (list
     'lambda
     '(witness)
     (list 'if
           qualification
           (putnam-1978-a4-quoted nil)
           (putnam-1978-a4-quoted t)))))

(defun putnam-1978-a4-finite-witness-valid-p (witness)
  (let ((failure-function
         (putnam-1978-a4-finite-witness-failure-function)))
    (and
     (tamep-functionp failure-function)
     (not (apply$ failure-function (list witness))))))

(defun-sk putnam-1978-a4-finite-witness-exists-p ()
  (exists (witness)
    (putnam-1978-a4-finite-witness-valid-p witness)))

(defun putnambench-putnam-1978-a4-statement
    (a b c d)
  (and
   (implies
    (and
     (putnam-1978-a4-algebra-p)
     (putnam-1978-a4-member-p a)
     (putnam-1978-a4-member-p b)
     (putnam-1978-a4-member-p c)
     (equal
      (putnam-1978-a4-multiply a b)
      c))
    (equal
     (putnam-1978-a4-multiply c c)
     c))
   (implies
    (and
     (putnam-1978-a4-algebra-p)
     (putnam-1978-a4-member-p a)
     (putnam-1978-a4-member-p b)
     (putnam-1978-a4-member-p c)
     (putnam-1978-a4-member-p d)
     (equal
      (putnam-1978-a4-multiply a b)
      c))
    (equal
     (putnam-1978-a4-multiply a d)
     (putnam-1978-a4-multiply c d)))
   (putnam-1978-a4-finite-witness-exists-p)))

(value-triple :itpeval-statement-checked)
:q
