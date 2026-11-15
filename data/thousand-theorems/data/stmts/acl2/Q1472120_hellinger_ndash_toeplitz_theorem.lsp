;; Statement-only formalization of thousand-theorems corpus artifact Q1472120,
;; "Hellinger&ndash;Toeplitz theorem": every symmetric linear operator on a
;; complete real or complex inner-product space is continuous. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Carriers, operations, vectors, sequences, and operators are tame APPLY$
;; function objects. FN-EQUAL supplies unbounded universal quantification, and
;; inequality with a constant-false function supplies internal existential
;; witnesses. Norms are represented by rational upper cuts, so their values
;; are genuine nonnegative reals rather than rational approximations.
;;
;; The scalar structure is explicitly a presentation of either the real field
;; or its complexification. Completeness is metric completeness, and continuity
;; is sequential continuity; for normed spaces these are equivalent to the
;; source notions. Linearity and symmetry are explicit hypotheses on the
;; arbitrary operator, and the conclusion is continuity of that same operator.

(defun q1472120-quoted (object)
  (list 'quote object))

(defun q1472120-term-list (terms)
  (if (consp terms)
      (list
       'cons
       (car terms)
       (q1472120-term-list (cdr terms)))
    (q1472120-quoted nil)))

(defun q1472120-apply-term (function-term arguments)
  (list
   'apply$
   function-term
   (q1472120-term-list arguments)))

(defun q1472120-static-apply-term (function arguments)
  (q1472120-apply-term
   (q1472120-quoted function)
   arguments))

(defun q1472120-and-terms (terms)
  (if (consp terms)
      (list
       'if
       (car terms)
       (q1472120-and-terms (cdr terms))
       (q1472120-quoted nil))
    (q1472120-quoted t)))

(defun q1472120-not-term (term)
  (list
   'if
   term
   (q1472120-quoted nil)
   (q1472120-quoted t)))

(defun q1472120-implies-term (hypothesis conclusion)
  (list
   'if
   hypothesis
   conclusion
   (q1472120-quoted t)))

(defun q1472120-iff-term (left right)
  (list
   'if
   left
   (list
    'if
    right
    (q1472120-quoted t)
    (q1472120-quoted nil))
   (list
    'if
    right
    (q1472120-quoted nil)
    (q1472120-quoted t))))

(defun q1472120-true-function (formals)
  (list 'lambda formals (q1472120-quoted t)))

(defun q1472120-fn-equal-true-p (function formals)
  (let ((always-true
         (q1472120-true-function formals)))
    (and
     (tamep-functionp function)
     (tamep-functionp always-true)
     (fn-equal function always-true))))

(defun q1472120-member-p (predicate object)
  (if (apply$ predicate (list object))
      t
    nil))

(defun q1472120-binary-value (function left right)
  (apply$ function (list left right)))

(defun q1472120-positive-rational-p (q)
  (and (rationalp q) (< 0 q)))

(defun q1472120-norm-lt-p (norm-lt object q)
  (if (apply$ norm-lt (list object q))
      t
    nil))

(defun q1472120-norm-finite-witness-p
    (norm-lt object q)
  (and
   (q1472120-positive-rational-p q)
   (q1472120-norm-lt-p norm-lt object q)))

(defun q1472120-norm-finite-failure-function
    (norm-lt object)
  (list
   'lambda
   '(q)
   (list
    'if
    (list
     'q1472120-norm-finite-witness-p
     (q1472120-quoted norm-lt)
     (q1472120-quoted object)
     'q)
    (q1472120-quoted nil)
    (q1472120-quoted t))))

(defun q1472120-norm-finite-p
    (norm-lt object)
  (let ((failure
         (q1472120-norm-finite-failure-function
          norm-lt object))
        (always-true
         (q1472120-true-function '(q))))
    (and
     (tamep-functionp failure)
     (tamep-functionp always-true)
     (not (fn-equal failure always-true)))))

(defun q1472120-norm-positive-witness-p
    (norm-lt object q)
  (and
   (q1472120-positive-rational-p q)
   (not (q1472120-norm-lt-p norm-lt object q))))

(defun q1472120-norm-positive-failure-function
    (norm-lt object)
  (list
   'lambda
   '(q)
   (list
    'if
    (list
     'q1472120-norm-positive-witness-p
     (q1472120-quoted norm-lt)
     (q1472120-quoted object)
     'q)
    (q1472120-quoted nil)
    (q1472120-quoted t))))

(defun q1472120-norm-positive-p
    (norm-lt object)
  (let ((failure
         (q1472120-norm-positive-failure-function
          norm-lt object))
        (always-true
         (q1472120-true-function '(q))))
    (and
     (tamep-functionp failure)
     (tamep-functionp always-true)
     (not (fn-equal failure always-true)))))

(defun q1472120-rounded-witness-p
    (norm-lt object q r)
  (and
   (q1472120-positive-rational-p r)
   (rationalp q)
   (< r q)
   (q1472120-norm-lt-p norm-lt object r)))

(defun q1472120-rounded-failure-function
    (norm-lt object q)
  (list
   'lambda
   '(r)
   (list
    'if
    (list
     'q1472120-rounded-witness-p
     (q1472120-quoted norm-lt)
     (q1472120-quoted object)
     (q1472120-quoted q)
     'r)
    (q1472120-quoted nil)
    (q1472120-quoted t))))

(defun q1472120-rounded-p
    (norm-lt object q)
  (let ((failure
         (q1472120-rounded-failure-function
          norm-lt object q))
        (always-true
         (q1472120-true-function '(r))))
    (and
     (tamep-functionp failure)
     (tamep-functionp always-true)
     (not (fn-equal failure always-true)))))

(defun q1472120-product-witness-p
    (norm-lt left right q witness)
  (let ((r (car witness))
        (s (cdr witness)))
    (and
     (q1472120-positive-rational-p q)
     (q1472120-positive-rational-p r)
     (q1472120-positive-rational-p s)
     (q1472120-norm-lt-p norm-lt left r)
     (q1472120-norm-lt-p norm-lt right s)
     (< (* r s) q))))

(defun q1472120-product-failure-function
    (norm-lt left right q)
  (list
   'lambda
   '(witness)
   (list
    'if
    (list
     'q1472120-product-witness-p
     (q1472120-quoted norm-lt)
     (q1472120-quoted left)
     (q1472120-quoted right)
     (q1472120-quoted q)
     'witness)
    (q1472120-quoted nil)
    (q1472120-quoted t))))

(defun q1472120-product-lt-p
    (norm-lt left right q)
  (let ((failure
         (q1472120-product-failure-function
          norm-lt left right q))
        (always-true
         (q1472120-true-function '(witness))))
    (and
     (q1472120-positive-rational-p q)
     (tamep-functionp failure)
     (tamep-functionp always-true)
     (not (fn-equal failure always-true)))))

(defun q1472120-mixed-product-witness-p
    (left-norm-lt right-norm-lt left right q witness)
  (let ((r (car witness))
        (s (cdr witness)))
    (and
     (q1472120-positive-rational-p q)
     (q1472120-positive-rational-p r)
     (q1472120-positive-rational-p s)
     (q1472120-norm-lt-p left-norm-lt left r)
     (q1472120-norm-lt-p right-norm-lt right s)
     (< (* r s) q))))

(defun q1472120-mixed-product-failure-function
    (left-norm-lt right-norm-lt left right q)
  (list
   'lambda
   '(witness)
   (list
    'if
    (list
     'q1472120-mixed-product-witness-p
     (q1472120-quoted left-norm-lt)
     (q1472120-quoted right-norm-lt)
     (q1472120-quoted left)
     (q1472120-quoted right)
     (q1472120-quoted q)
     'witness)
    (q1472120-quoted nil)
    (q1472120-quoted t))))

(defun q1472120-mixed-product-lt-p
    (left-norm-lt right-norm-lt left right q)
  (let ((failure
         (q1472120-mixed-product-failure-function
          left-norm-lt right-norm-lt
          left right q))
        (always-true
         (q1472120-true-function '(witness))))
    (and
     (q1472120-positive-rational-p q)
     (tamep-functionp failure)
     (tamep-functionp always-true)
     (not (fn-equal failure always-true)))))

(defun q1472120-field-row-function
    (carrier add multiply negate inverse zero one norm-lt)
  (let* ((xy-add
          (q1472120-static-apply-term add '(x y)))
         (yz-add
          (q1472120-static-apply-term add '(y z)))
         (xy-mul
          (q1472120-static-apply-term multiply '(x y)))
         (yz-mul
          (q1472120-static-apply-term multiply '(y z)))
         (neg-x
          (q1472120-static-apply-term negate '(x)))
         (inv-x
          (q1472120-static-apply-term inverse '(x))))
    (list
     'lambda
     '(x y z q r s)
     (q1472120-implies-term
      (q1472120-and-terms
       (list
        (q1472120-static-apply-term carrier '(x))
        (q1472120-static-apply-term carrier '(y))
        (q1472120-static-apply-term carrier '(z))))
      (q1472120-and-terms
       (list
        (q1472120-static-apply-term carrier
                                   (list xy-add))
        (q1472120-static-apply-term carrier
                                   (list xy-mul))
        (q1472120-static-apply-term carrier
                                   (list neg-x))
        (q1472120-implies-term
         (q1472120-not-term
          (list 'equal 'x (q1472120-quoted zero)))
         (q1472120-static-apply-term carrier
                                    (list inv-x)))
        (list
         'equal
         (q1472120-static-apply-term
          add
          (list xy-add 'z))
         (q1472120-static-apply-term
          add
          (list 'x yz-add)))
        (list
         'equal
         xy-add
         (q1472120-static-apply-term add '(y x)))
        (list
         'equal
         (q1472120-static-apply-term
          add
          (list 'x (q1472120-quoted zero)))
         'x)
        (list
         'equal
         (q1472120-static-apply-term
          add
          (list 'x neg-x))
         (q1472120-quoted zero))
        (list
         'equal
         (q1472120-static-apply-term
          multiply
          (list xy-mul 'z))
         (q1472120-static-apply-term
          multiply
          (list 'x yz-mul)))
        (list
         'equal
         xy-mul
         (q1472120-static-apply-term multiply '(y x)))
        (list
         'equal
         (q1472120-static-apply-term
          multiply
          (list 'x (q1472120-quoted one)))
         'x)
        (q1472120-implies-term
         (q1472120-not-term
          (list 'equal 'x (q1472120-quoted zero)))
         (list
          'equal
          (q1472120-static-apply-term
           multiply
           (list 'x inv-x))
          (q1472120-quoted one)))
        (list
         'equal
         (q1472120-static-apply-term
          multiply
          (list 'x yz-add))
         (q1472120-static-apply-term
          add
          (list
           (q1472120-static-apply-term
            multiply '(x y))
           (q1472120-static-apply-term
            multiply '(x z)))))
        (q1472120-implies-term
         (q1472120-static-apply-term norm-lt '(x q))
         (list
          'q1472120-positive-rational-p
          'q))
        (q1472120-implies-term
         (q1472120-and-terms
          (list
           (q1472120-static-apply-term norm-lt '(x q))
           (list 'rationalp 'r)
           (list '< 'q 'r)))
         (q1472120-static-apply-term norm-lt '(x r)))
        (q1472120-implies-term
         (q1472120-static-apply-term norm-lt '(x q))
         (list
          'q1472120-rounded-p
          (q1472120-quoted norm-lt)
          'x
          'q))
        (list
         'q1472120-norm-finite-p
         (q1472120-quoted norm-lt)
         'x)
        (q1472120-implies-term
         (q1472120-not-term
          (list 'equal 'x (q1472120-quoted zero)))
         (list
          'q1472120-norm-positive-p
          (q1472120-quoted norm-lt)
          'x))
        (q1472120-implies-term
         (list 'q1472120-positive-rational-p 'q)
         (q1472120-static-apply-term
          norm-lt
          (list (q1472120-quoted zero) 'q)))
        (q1472120-iff-term
         (q1472120-static-apply-term
          norm-lt
          (list neg-x 'q))
         (q1472120-static-apply-term norm-lt '(x q)))
        (q1472120-implies-term
         (q1472120-and-terms
          (list
           (list 'q1472120-positive-rational-p 'r)
           (list 'q1472120-positive-rational-p 's)
           (q1472120-static-apply-term norm-lt '(x r))
           (q1472120-static-apply-term norm-lt '(y s))))
         (q1472120-static-apply-term
          norm-lt
          (list
           xy-add
           (list '+ 'r 's))))
        (q1472120-iff-term
         (q1472120-static-apply-term
          norm-lt
          (list xy-mul 'q))
         (list
          'q1472120-product-lt-p
          (q1472120-quoted norm-lt)
          'x
          'y
          'q))))))))

(defun q1472120-nontrivial-norm-witness-p
    (carrier norm-lt witness)
  (let ((x (car witness))
        (q (cdr witness)))
    (and
     (q1472120-member-p carrier x)
     (rationalp q)
     (< 1 q)
     (not (q1472120-norm-lt-p norm-lt x q)))))

(defun q1472120-nontrivial-norm-failure-function
    (carrier norm-lt)
  (list
   'lambda
   '(witness)
   (list
    'if
    (list
     'q1472120-nontrivial-norm-witness-p
     (q1472120-quoted carrier)
     (q1472120-quoted norm-lt)
     'witness)
    (q1472120-quoted nil)
    (q1472120-quoted t))))

(defun q1472120-nontrivial-norm-p
    (carrier norm-lt)
  (let ((failure
         (q1472120-nontrivial-norm-failure-function
          carrier norm-lt))
        (always-true
         (q1472120-true-function '(witness))))
    (and
     (tamep-functionp failure)
     (tamep-functionp always-true)
     (not (fn-equal failure always-true)))))

(defun q1472120-nontrivially-normed-field-p
    (carrier add multiply negate inverse zero one norm-lt)
  (let ((row
         (q1472120-field-row-function
          carrier add multiply negate inverse
          zero one norm-lt)))
    (and
     (tamep-functionp carrier)
     (tamep-functionp add)
     (tamep-functionp multiply)
     (tamep-functionp negate)
     (tamep-functionp inverse)
     (tamep-functionp norm-lt)
     (q1472120-member-p carrier zero)
     (q1472120-member-p carrier one)
     (not (equal zero one))
     (equal (apply$ inverse (list zero)) zero)
     (q1472120-fn-equal-true-p
      row '(x y z q r s))
     (q1472120-nontrivial-norm-p
      carrier norm-lt))))

(defun q1472120-space-row-function
    (field-carrier field-add field-multiply field-one field-norm-lt
     carrier add negate zero scalar-multiply norm-lt)
  (let* ((xy-add
          (q1472120-static-apply-term add '(x y)))
         (yz-add
          (q1472120-static-apply-term add '(y z)))
         (neg-x
          (q1472120-static-apply-term negate '(x)))
         (a-smul-x
          (q1472120-static-apply-term scalar-multiply '(a x))))
    (list
     'lambda
     '(a b x y z q r s)
     (q1472120-implies-term
      (q1472120-and-terms
       (list
        (q1472120-static-apply-term field-carrier '(a))
        (q1472120-static-apply-term field-carrier '(b))
        (q1472120-static-apply-term carrier '(x))
        (q1472120-static-apply-term carrier '(y))
        (q1472120-static-apply-term carrier '(z))))
      (q1472120-and-terms
       (list
        (q1472120-static-apply-term carrier
                                   (list xy-add))
        (q1472120-static-apply-term carrier
                                   (list neg-x))
        (q1472120-static-apply-term carrier
                                   (list a-smul-x))
        (list
         'equal
         (q1472120-static-apply-term
          add
          (list xy-add 'z))
         (q1472120-static-apply-term
          add
          (list 'x yz-add)))
        (list
         'equal
         xy-add
         (q1472120-static-apply-term add '(y x)))
        (list
         'equal
         (q1472120-static-apply-term
          add
          (list 'x (q1472120-quoted zero)))
         'x)
        (list
         'equal
         (q1472120-static-apply-term
          add
          (list 'x neg-x))
         (q1472120-quoted zero))
        (list
         'equal
         (q1472120-static-apply-term
          scalar-multiply
          (list
           (q1472120-quoted field-one)
           'x))
         'x)
        (list
         'equal
         (q1472120-static-apply-term
          scalar-multiply
          (list
           (q1472120-static-apply-term
            field-multiply '(a b))
           'x))
         (q1472120-static-apply-term
          scalar-multiply
          (list
           'a
           (q1472120-static-apply-term
            scalar-multiply '(b x)))))
        (list
         'equal
         (q1472120-static-apply-term
          scalar-multiply
          (list
           (q1472120-static-apply-term
            field-add '(a b))
           'x))
         (q1472120-static-apply-term
          add
          (list
           a-smul-x
           (q1472120-static-apply-term
            scalar-multiply '(b x)))))
        (list
         'equal
         (q1472120-static-apply-term
          scalar-multiply
          (list 'a xy-add))
         (q1472120-static-apply-term
          add
          (list
           a-smul-x
           (q1472120-static-apply-term
            scalar-multiply '(a y)))))
        (q1472120-implies-term
         (q1472120-static-apply-term norm-lt '(x q))
         (list
          'q1472120-positive-rational-p
          'q))
        (q1472120-implies-term
         (q1472120-and-terms
          (list
           (q1472120-static-apply-term norm-lt '(x q))
           (list 'rationalp 'r)
           (list '< 'q 'r)))
         (q1472120-static-apply-term norm-lt '(x r)))
        (q1472120-implies-term
         (q1472120-static-apply-term norm-lt '(x q))
         (list
          'q1472120-rounded-p
          (q1472120-quoted norm-lt)
          'x
          'q))
        (list
         'q1472120-norm-finite-p
         (q1472120-quoted norm-lt)
         'x)
        (q1472120-implies-term
         (q1472120-not-term
          (list 'equal 'x (q1472120-quoted zero)))
         (list
          'q1472120-norm-positive-p
          (q1472120-quoted norm-lt)
          'x))
        (q1472120-implies-term
         (list 'q1472120-positive-rational-p 'q)
         (q1472120-static-apply-term
          norm-lt
          (list (q1472120-quoted zero) 'q)))
        (q1472120-iff-term
         (q1472120-static-apply-term
          norm-lt
          (list neg-x 'q))
         (q1472120-static-apply-term norm-lt '(x q)))
        (q1472120-implies-term
         (q1472120-and-terms
          (list
           (list 'q1472120-positive-rational-p 'r)
           (list 'q1472120-positive-rational-p 's)
           (q1472120-static-apply-term norm-lt '(x r))
           (q1472120-static-apply-term norm-lt '(y s))))
         (q1472120-static-apply-term
          norm-lt
          (list
           xy-add
           (list '+ 'r 's))))
        (q1472120-iff-term
         (q1472120-static-apply-term
          norm-lt
          (list a-smul-x 'q))
         (list
          'q1472120-mixed-product-lt-p
          (q1472120-quoted field-norm-lt)
          (q1472120-quoted norm-lt)
          'a
          'x
          'q))))))))

(defun q1472120-sequence-valid-function
    (carrier sequence)
  (list
   'lambda
   '(n)
   (q1472120-implies-term
    (list 'natp 'n)
    (q1472120-static-apply-term
     carrier
     (list
      (q1472120-static-apply-term sequence '(n)))))))

(defun q1472120-sequence-valid-p
    (carrier sequence)
  (let ((law
         (q1472120-sequence-valid-function
          carrier sequence)))
    (and
     (tamep-functionp sequence)
     (q1472120-fn-equal-true-p law '(n)))))

(defun q1472120-norm-difference-lt-p
    (add negate norm-lt left right epsilon)
  (q1472120-norm-lt-p
   norm-lt
   (q1472120-binary-value
    add
    left
    (apply$ negate (list right)))
   epsilon))

(defun q1472120-cauchy-tail-function
    (add negate norm-lt sequence epsilon n0)
  (list
   'lambda
   '(m n)
   (q1472120-implies-term
    (q1472120-and-terms
     (list
      (list 'natp 'm)
      (list 'natp 'n)
      (list '<= (q1472120-quoted n0) 'm)
      (list '<= (q1472120-quoted n0) 'n)))
    (list
     'q1472120-norm-difference-lt-p
     (q1472120-quoted add)
     (q1472120-quoted negate)
     (q1472120-quoted norm-lt)
     (q1472120-static-apply-term sequence '(m))
     (q1472120-static-apply-term sequence '(n))
     (q1472120-quoted epsilon)))))

(defun q1472120-cauchy-tail-p
    (add negate norm-lt sequence epsilon n0)
  (and
   (natp n0)
   (q1472120-fn-equal-true-p
    (q1472120-cauchy-tail-function
     add negate norm-lt sequence epsilon n0)
    '(m n))))

(defun q1472120-cauchy-epsilon-failure-function
    (add negate norm-lt sequence epsilon)
  (list
   'lambda
   '(n0)
   (list
    'if
    (list
     'q1472120-cauchy-tail-p
     (q1472120-quoted add)
     (q1472120-quoted negate)
     (q1472120-quoted norm-lt)
     (q1472120-quoted sequence)
     (q1472120-quoted epsilon)
     'n0)
    (q1472120-quoted nil)
    (q1472120-quoted t))))

(defun q1472120-cauchy-epsilon-p
    (add negate norm-lt sequence epsilon)
  (let ((failure
         (q1472120-cauchy-epsilon-failure-function
          add negate norm-lt sequence epsilon))
        (always-true
         (q1472120-true-function '(n0))))
    (and
     (q1472120-positive-rational-p epsilon)
     (tamep-functionp failure)
     (tamep-functionp always-true)
     (not (fn-equal failure always-true)))))

(defun q1472120-cauchy-function
    (add negate norm-lt sequence)
  (list
   'lambda
   '(epsilon)
   (q1472120-implies-term
    (list 'q1472120-positive-rational-p 'epsilon)
    (list
     'q1472120-cauchy-epsilon-p
     (q1472120-quoted add)
     (q1472120-quoted negate)
     (q1472120-quoted norm-lt)
     (q1472120-quoted sequence)
     'epsilon))))

(defun q1472120-cauchy-p
    (carrier add negate norm-lt sequence)
  (and
   (q1472120-sequence-valid-p carrier sequence)
   (q1472120-fn-equal-true-p
    (q1472120-cauchy-function
     add negate norm-lt sequence)
    '(epsilon))))

(defun q1472120-convergence-tail-function
    (add negate norm-lt sequence limit epsilon n0)
  (list
   'lambda
   '(n)
   (q1472120-implies-term
    (q1472120-and-terms
     (list
      (list 'natp 'n)
      (list '<= (q1472120-quoted n0) 'n)))
    (list
     'q1472120-norm-difference-lt-p
     (q1472120-quoted add)
     (q1472120-quoted negate)
     (q1472120-quoted norm-lt)
     (q1472120-static-apply-term sequence '(n))
     (q1472120-quoted limit)
     (q1472120-quoted epsilon)))))

(defun q1472120-convergence-tail-p
    (add negate norm-lt sequence limit epsilon n0)
  (and
   (natp n0)
   (q1472120-fn-equal-true-p
    (q1472120-convergence-tail-function
     add negate norm-lt sequence limit epsilon n0)
    '(n))))

(defun q1472120-convergence-epsilon-failure-function
    (add negate norm-lt sequence limit epsilon)
  (list
   'lambda
   '(n0)
   (list
    'if
    (list
     'q1472120-convergence-tail-p
     (q1472120-quoted add)
     (q1472120-quoted negate)
     (q1472120-quoted norm-lt)
     (q1472120-quoted sequence)
     (q1472120-quoted limit)
     (q1472120-quoted epsilon)
     'n0)
    (q1472120-quoted nil)
    (q1472120-quoted t))))

(defun q1472120-convergence-epsilon-p
    (add negate norm-lt sequence limit epsilon)
  (let ((failure
         (q1472120-convergence-epsilon-failure-function
          add negate norm-lt sequence limit epsilon))
        (always-true
         (q1472120-true-function '(n0))))
    (and
     (q1472120-positive-rational-p epsilon)
     (tamep-functionp failure)
     (tamep-functionp always-true)
     (not (fn-equal failure always-true)))))

(defun q1472120-convergence-function
    (add negate norm-lt sequence limit)
  (list
   'lambda
   '(epsilon)
   (q1472120-implies-term
    (list 'q1472120-positive-rational-p 'epsilon)
    (list
     'q1472120-convergence-epsilon-p
     (q1472120-quoted add)
     (q1472120-quoted negate)
     (q1472120-quoted norm-lt)
     (q1472120-quoted sequence)
     (q1472120-quoted limit)
     'epsilon))))

(defun q1472120-converges-p
    (carrier add negate norm-lt sequence limit)
  (and
   (q1472120-member-p carrier limit)
   (q1472120-sequence-valid-p carrier sequence)
   (q1472120-fn-equal-true-p
    (q1472120-convergence-function
     add negate norm-lt sequence limit)
    '(epsilon))))

(defun q1472120-limit-witness-p
    (carrier add negate norm-lt sequence limit)
  (and
   (q1472120-member-p carrier limit)
   (q1472120-converges-p
    carrier add negate norm-lt sequence limit)))

(defun q1472120-limit-failure-function
    (carrier add negate norm-lt sequence)
  (list
   'lambda
   '(limit)
   (list
    'if
    (list
     'q1472120-limit-witness-p
     (q1472120-quoted carrier)
     (q1472120-quoted add)
     (q1472120-quoted negate)
     (q1472120-quoted norm-lt)
     (q1472120-quoted sequence)
     'limit)
    (q1472120-quoted nil)
    (q1472120-quoted t))))

(defun q1472120-limit-exists-p
    (carrier add negate norm-lt sequence)
  (let ((failure
         (q1472120-limit-failure-function
          carrier add negate norm-lt sequence))
        (always-true
         (q1472120-true-function '(limit))))
    (and
     (tamep-functionp failure)
     (tamep-functionp always-true)
     (not (fn-equal failure always-true)))))

(defun q1472120-completeness-function
    (carrier add negate norm-lt)
  (list
   'lambda
   '(sequence)
   (q1472120-implies-term
    (list
     'q1472120-cauchy-p
     (q1472120-quoted carrier)
     (q1472120-quoted add)
     (q1472120-quoted negate)
     (q1472120-quoted norm-lt)
     'sequence)
    (list
     'q1472120-limit-exists-p
     (q1472120-quoted carrier)
     (q1472120-quoted add)
     (q1472120-quoted negate)
     (q1472120-quoted norm-lt)
     'sequence))))

(defun q1472120-banach-space-p
    (field-carrier field-add field-multiply field-one field-norm-lt
     carrier add negate zero scalar-multiply norm-lt)
  (let ((row
         (q1472120-space-row-function
          field-carrier field-add field-multiply
          field-one field-norm-lt
          carrier add negate zero scalar-multiply norm-lt))
        (complete
         (q1472120-completeness-function
          carrier add negate norm-lt)))
    (and
     (tamep-functionp carrier)
     (tamep-functionp add)
     (tamep-functionp negate)
     (tamep-functionp scalar-multiply)
     (tamep-functionp norm-lt)
     (q1472120-member-p carrier zero)
     (q1472120-fn-equal-true-p
      row '(a b x y z q r s))
     (q1472120-fn-equal-true-p
      complete '(sequence)))))

(defun q1472120-linear-map-function
    (field-carrier domain-carrier codomain-carrier
     domain-add codomain-add
     domain-smul codomain-smul mapping)
  (list
   'lambda
   '(a x y)
   (q1472120-implies-term
    (q1472120-and-terms
     (list
      (q1472120-static-apply-term field-carrier '(a))
      (q1472120-static-apply-term domain-carrier '(x))
      (q1472120-static-apply-term domain-carrier '(y))))
    (q1472120-and-terms
     (list
      (q1472120-static-apply-term
       codomain-carrier
       (list
        (q1472120-static-apply-term mapping '(x))))
      (list
       'equal
       (q1472120-static-apply-term
        mapping
        (list
         (q1472120-static-apply-term domain-add '(x y))))
       (q1472120-static-apply-term
        codomain-add
        (list
         (q1472120-static-apply-term mapping '(x))
         (q1472120-static-apply-term mapping '(y)))))
      (list
       'equal
       (q1472120-static-apply-term
        mapping
        (list
         (q1472120-static-apply-term domain-smul '(a x))))
       (q1472120-static-apply-term
        codomain-smul
        (list
         'a
         (q1472120-static-apply-term mapping '(x))))))))))

(defun q1472120-linear-map-p
    (field-carrier domain-carrier codomain-carrier
     domain-add codomain-add
     domain-smul codomain-smul mapping)
  (and
   (tamep-functionp mapping)
   (q1472120-fn-equal-true-p
    (q1472120-linear-map-function
     field-carrier domain-carrier codomain-carrier
     domain-add codomain-add
     domain-smul codomain-smul mapping)
    '(a x y))))

(defun q1472120-compose-sequence
    (mapping sequence)
  (list
   'lambda
   '(n)
   (q1472120-static-apply-term
    mapping
    (list
     (q1472120-static-apply-term sequence '(n))))))

(defun q1472120-continuity-function
    (domain-carrier domain-add domain-negate domain-norm-lt
     codomain-carrier codomain-add codomain-negate codomain-norm-lt
     mapping)
  (list
   'lambda
   '(sequence x)
   (q1472120-implies-term
    (list
     'q1472120-converges-p
     (q1472120-quoted domain-carrier)
     (q1472120-quoted domain-add)
     (q1472120-quoted domain-negate)
     (q1472120-quoted domain-norm-lt)
     'sequence
     'x)
    (list
     'q1472120-converges-p
     (q1472120-quoted codomain-carrier)
     (q1472120-quoted codomain-add)
     (q1472120-quoted codomain-negate)
     (q1472120-quoted codomain-norm-lt)
     (list
      'q1472120-compose-sequence
      (q1472120-quoted mapping)
      'sequence)
     (q1472120-static-apply-term mapping '(x))))))

(defun q1472120-continuous-p
    (domain-carrier domain-add domain-negate domain-norm-lt
     codomain-carrier codomain-add codomain-negate codomain-norm-lt
     mapping)
  (q1472120-fn-equal-true-p
   (q1472120-continuity-function
    domain-carrier domain-add domain-negate domain-norm-lt
    codomain-carrier codomain-add codomain-negate codomain-norm-lt
    mapping)
   '(sequence x)))

(defun q1472120-or-terms (terms)
  (if (consp terms)
      (list
       'if
       (car terms)
       (q1472120-quoted t)
       (q1472120-or-terms (cdr terms)))
    (q1472120-quoted nil)))

(defun q1472120-false-function (formals)
  (list 'lambda formals (q1472120-quoted nil)))

(defun q1472120-exists-p (function formals)
  (let ((always-false
         (q1472120-false-function formals)))
    (and
     (tamep-functionp function)
     (tamep-functionp always-false)
     (not (fn-equal function always-false)))))

;; Canonical rational casts into a presented field.

(defun q1472120-natural-cast (n zero one add)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      zero
    (q1472120-binary-value
     add one
     (q1472120-natural-cast (- n 1) zero one add))))

(defun q1472120-integer-cast
    (n zero one add negate)
  (if (and (integerp n) (< n 0))
      (apply$
       negate
       (list
        (q1472120-natural-cast
         (- n) zero one add)))
    (q1472120-natural-cast
     (nfix n) zero one add)))

(defun q1472120-rational-cast
    (q zero one add multiply negate inverse)
  (if (rationalp q)
      (q1472120-binary-value
       multiply
       (q1472120-integer-cast
        (numerator q) zero one add negate)
       (apply$
        inverse
        (list
         (q1472120-integer-cast
          (denominator q) zero one add negate))))
    zero))

;; A complete Archimedean ordered-field presentation of the real numbers.
;; Archimedeanness follows from the rationally finite absolute-value cuts.

(defun q1472120-order-laws-function
    (carrier zero add multiply less)
  (let ((xy (q1472120-static-apply-term less '(x y)))
        (yx (q1472120-static-apply-term less '(y x)))
        (yz (q1472120-static-apply-term less '(y z))))
    (list
     'lambda
     '(x y z)
     (q1472120-implies-term
      (q1472120-and-terms
       (list
        (q1472120-static-apply-term carrier '(x))
        (q1472120-static-apply-term carrier '(y))
        (q1472120-static-apply-term carrier '(z))))
      (q1472120-and-terms
       (list
        (q1472120-not-term
         (q1472120-static-apply-term less '(x x)))
        (q1472120-or-terms
         (list xy yx (list 'equal 'x 'y)))
        (q1472120-implies-term
         (q1472120-and-terms (list xy yz))
         (q1472120-static-apply-term less '(x z)))
        (q1472120-implies-term
         xy
         (q1472120-static-apply-term
          less
          (list
           (q1472120-static-apply-term add '(x z))
           (q1472120-static-apply-term add '(y z)))))
        (q1472120-implies-term
         (q1472120-and-terms
          (list
           (q1472120-static-apply-term
            less
            (list (q1472120-quoted zero) 'x))
           (q1472120-static-apply-term
            less
            (list (q1472120-quoted zero) 'y))))
         (q1472120-static-apply-term
          less
          (list
           (q1472120-quoted zero)
           (q1472120-static-apply-term
            multiply '(x y)))))))))))

(defun q1472120-real-norm-order-function
    (carrier zero one add multiply negate inverse less norm-lt)
  (let* ((cast-q
          (list
           'q1472120-rational-cast
           'q
           (q1472120-quoted zero)
           (q1472120-quoted one)
           (q1472120-quoted add)
           (q1472120-quoted multiply)
           (q1472120-quoted negate)
           (q1472120-quoted inverse)))
         (neg-cast-q
          (q1472120-static-apply-term
           negate
           (list cast-q))))
    (list
     'lambda
     '(x q)
     (q1472120-implies-term
      (q1472120-static-apply-term carrier '(x))
      (q1472120-iff-term
       (q1472120-static-apply-term norm-lt '(x q))
       (q1472120-and-terms
        (list
         (list 'q1472120-positive-rational-p 'q)
         (q1472120-static-apply-term less
                                    (list neg-cast-q 'x))
         (q1472120-static-apply-term less
                                    (list 'x cast-q)))))))))

(defun q1472120-real-field-p
    (carrier add multiply negate inverse zero one less norm-lt)
  (and
   (q1472120-nontrivially-normed-field-p
    carrier add multiply negate inverse zero one norm-lt)
   (tamep-functionp less)
   (q1472120-fn-equal-true-p
    (q1472120-order-laws-function
     carrier zero add multiply less)
    '(x y z))
   (q1472120-binary-value less zero one)
   (q1472120-fn-equal-true-p
    (q1472120-real-norm-order-function
     carrier zero one add multiply negate inverse less norm-lt)
    '(x q))
   (q1472120-banach-space-p
    carrier add multiply one norm-lt
    carrier add negate zero multiply norm-lt)))

;; An RCLike scalar field is either the real presentation above or its
;; quadratic complexification. RE, IM, OF-REAL, STAR, and I give coordinates
;; and conjugation, while the norm cut is tied to re(x)^2 + im(x)^2.

(defun q1472120-rclike-coordinate-function
    (complexp
     real-carrier real-add real-multiply real-negate real-inverse
     real-zero real-one real-less
     scalar-carrier scalar-add scalar-multiply scalar-negate
     scalar-norm-lt
     of-real real-part imag-part star imaginary-unit)
  (let* ((re-x
          (q1472120-static-apply-term real-part '(x)))
         (im-x
          (q1472120-static-apply-term imag-part '(x)))
         (of-re-x
          (q1472120-static-apply-term of-real (list re-x)))
         (of-im-x
          (q1472120-static-apply-term of-real (list im-x)))
         (im-i
          (q1472120-static-apply-term
           scalar-multiply
           (list of-im-x
                 (q1472120-quoted imaginary-unit))))
         (coordinate-sum
          (q1472120-static-apply-term
           scalar-add
           (list of-re-x im-i)))
         (star-coordinate
          (q1472120-static-apply-term
           scalar-add
           (list
            of-re-x
            (q1472120-static-apply-term
             scalar-negate
             (list im-i)))))
         (of-r
          (q1472120-static-apply-term of-real '(r)))
         (of-s
          (q1472120-static-apply-term of-real '(s)))
         (cast-q
          (list
           'q1472120-rational-cast
           'q
           (q1472120-quoted real-zero)
           (q1472120-quoted real-one)
           (q1472120-quoted real-add)
           (q1472120-quoted real-multiply)
           (q1472120-quoted real-negate)
           (q1472120-quoted real-inverse)))
         (q-square
          (q1472120-static-apply-term
           real-multiply
           (list cast-q cast-q)))
         (re-square
          (q1472120-static-apply-term
           real-multiply
           (list re-x re-x)))
         (im-square
          (q1472120-static-apply-term
           real-multiply
           (list im-x im-x)))
         (modulus-square
          (q1472120-static-apply-term
           real-add
           (list re-square im-square))))
    (list
     'lambda
     '(x r s q)
     (q1472120-and-terms
      (list
       (q1472120-implies-term
        (q1472120-static-apply-term scalar-carrier '(x))
        (q1472120-and-terms
         (list
          (q1472120-static-apply-term real-carrier
                                     (list re-x))
          (q1472120-static-apply-term real-carrier
                                     (list im-x))
          (q1472120-static-apply-term scalar-carrier
                                     (list
                                      (q1472120-static-apply-term
                                       star '(x))))
          (q1472120-implies-term
           (q1472120-quoted complexp)
           (q1472120-and-terms
            (list
             (list 'equal 'x coordinate-sum)
             (list
              'equal
              (q1472120-static-apply-term star '(x))
              star-coordinate))))
          (q1472120-implies-term
           (q1472120-not-term
            (q1472120-quoted complexp))
           (q1472120-and-terms
            (list
             (list 'equal 'x of-re-x)
             (list 'equal im-x
                   (q1472120-quoted real-zero))
             (list
              'equal
              (q1472120-static-apply-term star '(x))
              'x))))
          (q1472120-iff-term
           (q1472120-static-apply-term scalar-norm-lt '(x q))
           (q1472120-and-terms
            (list
             (list 'q1472120-positive-rational-p 'q)
             (q1472120-static-apply-term
              real-less
              (list modulus-square q-square))))))))
       (q1472120-implies-term
        (q1472120-and-terms
         (list
          (q1472120-static-apply-term real-carrier '(r))
          (q1472120-static-apply-term real-carrier '(s))))
        (q1472120-and-terms
         (list
          (q1472120-static-apply-term scalar-carrier
                                     (list of-r))
          (list
           'equal
           (q1472120-static-apply-term real-part
                                      (list of-r))
           'r)
          (list
           'equal
           (q1472120-static-apply-term imag-part
                                      (list of-r))
           (q1472120-quoted real-zero))
          (list
           'equal
           (q1472120-static-apply-term
            of-real
            (list
             (q1472120-static-apply-term
              real-add '(r s))))
           (q1472120-static-apply-term
            scalar-add
            (list of-r of-s)))
          (list
           'equal
           (q1472120-static-apply-term
            of-real
            (list
             (q1472120-static-apply-term
              real-multiply '(r s))))
           (q1472120-static-apply-term
            scalar-multiply
            (list of-r of-s)))
          (list
           'equal
           (q1472120-static-apply-term
            of-real
            (list
             (q1472120-static-apply-term
              real-negate '(r))))
           (q1472120-static-apply-term
            scalar-negate
            (list of-r)))))))))))

(defun q1472120-rclike-field-p
    (complexp
     real-carrier real-add real-multiply real-negate real-inverse
     real-zero real-one real-less real-norm-lt
     scalar-carrier scalar-add scalar-multiply scalar-negate scalar-inverse
     scalar-zero scalar-one scalar-norm-lt
     of-real real-part imag-part star imaginary-unit)
  (and
   (booleanp complexp)
   (q1472120-real-field-p
    real-carrier real-add real-multiply real-negate real-inverse
    real-zero real-one real-less real-norm-lt)
   (q1472120-nontrivially-normed-field-p
    scalar-carrier scalar-add scalar-multiply scalar-negate scalar-inverse
    scalar-zero scalar-one scalar-norm-lt)
   (tamep-functionp of-real)
   (tamep-functionp real-part)
   (tamep-functionp imag-part)
   (tamep-functionp star)
   (q1472120-member-p scalar-carrier imaginary-unit)
   (equal (apply$ of-real (list real-zero)) scalar-zero)
   (equal (apply$ of-real (list real-one)) scalar-one)
   (equal (apply$ real-part (list scalar-zero)) real-zero)
   (equal (apply$ imag-part (list scalar-zero)) real-zero)
   (equal (apply$ real-part (list scalar-one)) real-one)
   (equal (apply$ imag-part (list scalar-one)) real-zero)
   (if complexp
       (and
        (equal
         (apply$ real-part (list imaginary-unit))
         real-zero)
        (equal
         (apply$ imag-part (list imaginary-unit))
         real-one)
        (equal
         (q1472120-binary-value
          scalar-multiply imaginary-unit imaginary-unit)
         (apply$ scalar-negate (list scalar-one))))
     (equal imaginary-unit scalar-zero))
   (q1472120-fn-equal-true-p
    (q1472120-rclike-coordinate-function
     complexp
     real-carrier real-add real-multiply real-negate real-inverse
     real-zero real-one real-less
     scalar-carrier scalar-add scalar-multiply scalar-negate
     scalar-norm-lt
     of-real real-part imag-part star imaginary-unit)
    '(x r s q))))

;; Inner-product spaces, with the norm cut definitionally tied to
;; re(<x,x>). The second argument is linear, matching mathlib's convention.

(defun q1472120-inner-product-laws-function
    (real-add real-multiply real-negate real-inverse
     real-zero real-one real-less
     scalar-carrier scalar-add scalar-multiply scalar-zero
     real-part star
     carrier add zero smul norm-lt inner)
  (let* ((xy-inner
          (q1472120-static-apply-term inner '(x y)))
         (yx-inner
          (q1472120-static-apply-term inner '(y x)))
         (xx-inner
          (q1472120-static-apply-term inner '(x x)))
         (xx-real
          (q1472120-static-apply-term
           real-part
           (list xx-inner)))
         (cast-q
          (list
           'q1472120-rational-cast
           'q
           (q1472120-quoted real-zero)
           (q1472120-quoted real-one)
           (q1472120-quoted real-add)
           (q1472120-quoted real-multiply)
           (q1472120-quoted real-negate)
           (q1472120-quoted real-inverse)))
         (q-square
          (q1472120-static-apply-term
           real-multiply
           (list cast-q cast-q))))
    (list
     'lambda
     '(a x y z q)
     (q1472120-implies-term
      (q1472120-and-terms
       (list
        (q1472120-static-apply-term scalar-carrier '(a))
        (q1472120-static-apply-term carrier '(x))
        (q1472120-static-apply-term carrier '(y))
        (q1472120-static-apply-term carrier '(z))))
      (q1472120-and-terms
       (list
        (q1472120-static-apply-term scalar-carrier
                                   (list xy-inner))
        (list
         'equal
         (q1472120-static-apply-term
          inner
          (list
           'x
           (q1472120-static-apply-term add '(y z))))
         (q1472120-static-apply-term
          scalar-add
          (list
           xy-inner
           (q1472120-static-apply-term inner '(x z)))))
        (list
         'equal
         (q1472120-static-apply-term
          inner
          (list
           'x
           (q1472120-static-apply-term smul '(a y))))
         (q1472120-static-apply-term
          scalar-multiply
          (list 'a xy-inner)))
        (list
         'equal
         yx-inner
         (q1472120-static-apply-term
          star
          (list xy-inner)))
        (q1472120-not-term
         (q1472120-static-apply-term
          real-less
          (list xx-real
                (q1472120-quoted real-zero))))
        (q1472120-iff-term
         (list 'equal xx-inner
               (q1472120-quoted scalar-zero))
         (list 'equal 'x
               (q1472120-quoted zero)))
        (q1472120-iff-term
         (q1472120-static-apply-term norm-lt '(x q))
         (q1472120-and-terms
          (list
           (list 'q1472120-positive-rational-p 'q)
           (q1472120-static-apply-term
            real-less
            (list xx-real q-square)))))))))))

(defun q1472120-hilbert-space-p
    (real-add real-multiply real-negate real-inverse
     real-zero real-one real-less
     scalar-carrier scalar-add scalar-multiply scalar-one scalar-norm-lt
     scalar-zero real-part star
     carrier add negate zero smul norm-lt inner)
  (and
   (q1472120-banach-space-p
    scalar-carrier scalar-add scalar-multiply scalar-one scalar-norm-lt
    carrier add negate zero smul norm-lt)
   (tamep-functionp inner)
   (q1472120-fn-equal-true-p
    (q1472120-inner-product-laws-function
     real-add real-multiply real-negate real-inverse
     real-zero real-one real-less
     scalar-carrier scalar-add scalar-multiply scalar-zero
     real-part star
     carrier add zero smul norm-lt inner)
    '(a x y z q))))

;; Symmetry is the source equation <T x,y> = <x,T y> for every pair of
;; vectors. The linear-map predicate also supplies closure of T on the carrier.

(defun q1472120-symmetry-function
    (carrier inner operator)
  (list
   'lambda
   '(x y)
   (q1472120-implies-term
    (q1472120-and-terms
     (list
      (q1472120-static-apply-term carrier '(x))
      (q1472120-static-apply-term carrier '(y))))
    (list
     'equal
     (q1472120-static-apply-term
      inner
      (list
       (q1472120-static-apply-term operator '(x))
       'y))
     (q1472120-static-apply-term
      inner
      (list
       'x
       (q1472120-static-apply-term operator '(y))))))))

(defun q1472120-symmetric-linear-operator-p
    (scalar-carrier carrier add smul inner operator)
  (and
   (q1472120-linear-map-p
    scalar-carrier carrier carrier
    add add smul smul operator)
   (q1472120-fn-equal-true-p
    (q1472120-symmetry-function
     carrier inner operator)
    '(x y))))

(defun thousand-theorems-q1472120-hellinger-toeplitz-theorem-statement
    (complexp
     real-carrier real-add real-multiply real-negate real-inverse
     real-zero real-one real-less real-norm-lt
     scalar-carrier scalar-add scalar-multiply scalar-negate scalar-inverse
     scalar-zero scalar-one scalar-norm-lt
     of-real real-part imag-part star imaginary-unit
     carrier add negate zero smul norm-lt inner operator)
  (implies
   (and
    (q1472120-rclike-field-p
     complexp
     real-carrier real-add real-multiply real-negate real-inverse
     real-zero real-one real-less real-norm-lt
     scalar-carrier scalar-add scalar-multiply scalar-negate scalar-inverse
     scalar-zero scalar-one scalar-norm-lt
     of-real real-part imag-part star imaginary-unit)
    (q1472120-hilbert-space-p
     real-add real-multiply real-negate real-inverse
     real-zero real-one real-less
     scalar-carrier scalar-add scalar-multiply scalar-one scalar-norm-lt
     scalar-zero real-part star
     carrier add negate zero smul norm-lt inner)
    (q1472120-symmetric-linear-operator-p
     scalar-carrier carrier add smul inner operator))
   (q1472120-continuous-p
    carrier add negate norm-lt
    carrier add negate norm-lt
    operator)))

(value-triple :itpeval-statement-checked)
:q
