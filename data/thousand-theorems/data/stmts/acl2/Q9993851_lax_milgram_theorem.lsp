;; Statement-only formalization of thousand-theorems corpus artifact Q9993851,
;; "Lax–Milgram theorem": a coercive bounded bilinear form on a complete real
;; inner-product space induces a continuous linear equivalence representing
;; the form through the inner product. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Tame APPLY$ functions represent the real field, Hilbert-space carrier,
;; operations, sequences, and maps. FN-EQUAL supplies unbounded universal
;; quantification, and inequality with a constant-false function supplies
;; internal existential witnesses. Norms are represented by rational upper
;; cuts, which encode genuine nonnegative real values rather than restricting
;; norms to rational values.
;;
;; Joint sequential continuity of the bilinear map is equivalent to bounded
;; bilinearity on normed spaces. Coercivity uses inner(u,u) = ||u||^2 and an
;; internally quantified positive rational constant; density of the rationals
;; makes this equivalent to the source's positive real constant. The conclusion
;; internally quantifies the mutually inverse continuous linear maps.

(defun q9993851-quoted (object)
  (list 'quote object))

(defun q9993851-term-list (terms)
  (if (consp terms)
      (list
       'cons
       (car terms)
       (q9993851-term-list (cdr terms)))
    (q9993851-quoted nil)))

(defun q9993851-apply-term (function-term arguments)
  (list
   'apply$
   function-term
   (q9993851-term-list arguments)))

(defun q9993851-static-apply-term (function arguments)
  (q9993851-apply-term
   (q9993851-quoted function)
   arguments))

(defun q9993851-and-terms (terms)
  (if (consp terms)
      (list
       'if
       (car terms)
       (q9993851-and-terms (cdr terms))
       (q9993851-quoted nil))
    (q9993851-quoted t)))

(defun q9993851-not-term (term)
  (list
   'if
   term
   (q9993851-quoted nil)
   (q9993851-quoted t)))

(defun q9993851-implies-term (hypothesis conclusion)
  (list
   'if
   hypothesis
   conclusion
   (q9993851-quoted t)))

(defun q9993851-iff-term (left right)
  (list
   'if
   left
   (list
    'if
    right
    (q9993851-quoted t)
    (q9993851-quoted nil))
   (list
    'if
    right
    (q9993851-quoted nil)
    (q9993851-quoted t))))

(defun q9993851-true-function (formals)
  (list 'lambda formals (q9993851-quoted t)))

(defun q9993851-fn-equal-true-p (function formals)
  (let ((always-true
         (q9993851-true-function formals)))
    (and
     (tamep-functionp function)
     (tamep-functionp always-true)
     (fn-equal function always-true))))

(defun q9993851-member-p (predicate object)
  (if (apply$ predicate (list object))
      t
    nil))

(defun q9993851-binary-value (function left right)
  (apply$ function (list left right)))

(defun q9993851-positive-rational-p (q)
  (and (rationalp q) (< 0 q)))

(defun q9993851-norm-lt-p (norm-lt object q)
  (if (apply$ norm-lt (list object q))
      t
    nil))

(defun q9993851-norm-finite-witness-p
    (norm-lt object q)
  (and
   (q9993851-positive-rational-p q)
   (q9993851-norm-lt-p norm-lt object q)))

(defun q9993851-norm-finite-failure-function
    (norm-lt object)
  (list
   'lambda
   '(q)
   (list
    'if
    (list
     'q9993851-norm-finite-witness-p
     (q9993851-quoted norm-lt)
     (q9993851-quoted object)
     'q)
    (q9993851-quoted nil)
    (q9993851-quoted t))))

(defun q9993851-norm-finite-p
    (norm-lt object)
  (let ((failure
         (q9993851-norm-finite-failure-function
          norm-lt object))
        (always-true
         (q9993851-true-function '(q))))
    (and
     (tamep-functionp failure)
     (tamep-functionp always-true)
     (not (fn-equal failure always-true)))))

(defun q9993851-norm-positive-witness-p
    (norm-lt object q)
  (and
   (q9993851-positive-rational-p q)
   (not (q9993851-norm-lt-p norm-lt object q))))

(defun q9993851-norm-positive-failure-function
    (norm-lt object)
  (list
   'lambda
   '(q)
   (list
    'if
    (list
     'q9993851-norm-positive-witness-p
     (q9993851-quoted norm-lt)
     (q9993851-quoted object)
     'q)
    (q9993851-quoted nil)
    (q9993851-quoted t))))

(defun q9993851-norm-positive-p
    (norm-lt object)
  (let ((failure
         (q9993851-norm-positive-failure-function
          norm-lt object))
        (always-true
         (q9993851-true-function '(q))))
    (and
     (tamep-functionp failure)
     (tamep-functionp always-true)
     (not (fn-equal failure always-true)))))

(defun q9993851-rounded-witness-p
    (norm-lt object q r)
  (and
   (q9993851-positive-rational-p r)
   (rationalp q)
   (< r q)
   (q9993851-norm-lt-p norm-lt object r)))

(defun q9993851-rounded-failure-function
    (norm-lt object q)
  (list
   'lambda
   '(r)
   (list
    'if
    (list
     'q9993851-rounded-witness-p
     (q9993851-quoted norm-lt)
     (q9993851-quoted object)
     (q9993851-quoted q)
     'r)
    (q9993851-quoted nil)
    (q9993851-quoted t))))

(defun q9993851-rounded-p
    (norm-lt object q)
  (let ((failure
         (q9993851-rounded-failure-function
          norm-lt object q))
        (always-true
         (q9993851-true-function '(r))))
    (and
     (tamep-functionp failure)
     (tamep-functionp always-true)
     (not (fn-equal failure always-true)))))

(defun q9993851-product-witness-p
    (norm-lt left right q witness)
  (let ((r (car witness))
        (s (cdr witness)))
    (and
     (q9993851-positive-rational-p q)
     (q9993851-positive-rational-p r)
     (q9993851-positive-rational-p s)
     (q9993851-norm-lt-p norm-lt left r)
     (q9993851-norm-lt-p norm-lt right s)
     (< (* r s) q))))

(defun q9993851-product-failure-function
    (norm-lt left right q)
  (list
   'lambda
   '(witness)
   (list
    'if
    (list
     'q9993851-product-witness-p
     (q9993851-quoted norm-lt)
     (q9993851-quoted left)
     (q9993851-quoted right)
     (q9993851-quoted q)
     'witness)
    (q9993851-quoted nil)
    (q9993851-quoted t))))

(defun q9993851-product-lt-p
    (norm-lt left right q)
  (let ((failure
         (q9993851-product-failure-function
          norm-lt left right q))
        (always-true
         (q9993851-true-function '(witness))))
    (and
     (q9993851-positive-rational-p q)
     (tamep-functionp failure)
     (tamep-functionp always-true)
     (not (fn-equal failure always-true)))))

(defun q9993851-mixed-product-witness-p
    (left-norm-lt right-norm-lt left right q witness)
  (let ((r (car witness))
        (s (cdr witness)))
    (and
     (q9993851-positive-rational-p q)
     (q9993851-positive-rational-p r)
     (q9993851-positive-rational-p s)
     (q9993851-norm-lt-p left-norm-lt left r)
     (q9993851-norm-lt-p right-norm-lt right s)
     (< (* r s) q))))

(defun q9993851-mixed-product-failure-function
    (left-norm-lt right-norm-lt left right q)
  (list
   'lambda
   '(witness)
   (list
    'if
    (list
     'q9993851-mixed-product-witness-p
     (q9993851-quoted left-norm-lt)
     (q9993851-quoted right-norm-lt)
     (q9993851-quoted left)
     (q9993851-quoted right)
     (q9993851-quoted q)
     'witness)
    (q9993851-quoted nil)
    (q9993851-quoted t))))

(defun q9993851-mixed-product-lt-p
    (left-norm-lt right-norm-lt left right q)
  (let ((failure
         (q9993851-mixed-product-failure-function
          left-norm-lt right-norm-lt
          left right q))
        (always-true
         (q9993851-true-function '(witness))))
    (and
     (q9993851-positive-rational-p q)
     (tamep-functionp failure)
     (tamep-functionp always-true)
     (not (fn-equal failure always-true)))))

(defun q9993851-field-row-function
    (carrier add multiply negate inverse zero one norm-lt)
  (let* ((xy-add
          (q9993851-static-apply-term add '(x y)))
         (yz-add
          (q9993851-static-apply-term add '(y z)))
         (xy-mul
          (q9993851-static-apply-term multiply '(x y)))
         (yz-mul
          (q9993851-static-apply-term multiply '(y z)))
         (neg-x
          (q9993851-static-apply-term negate '(x)))
         (inv-x
          (q9993851-static-apply-term inverse '(x))))
    (list
     'lambda
     '(x y z q r s)
     (q9993851-implies-term
      (q9993851-and-terms
       (list
        (q9993851-static-apply-term carrier '(x))
        (q9993851-static-apply-term carrier '(y))
        (q9993851-static-apply-term carrier '(z))))
      (q9993851-and-terms
       (list
        (q9993851-static-apply-term carrier
                                   (list xy-add))
        (q9993851-static-apply-term carrier
                                   (list xy-mul))
        (q9993851-static-apply-term carrier
                                   (list neg-x))
        (q9993851-implies-term
         (q9993851-not-term
          (list 'equal 'x (q9993851-quoted zero)))
         (q9993851-static-apply-term carrier
                                    (list inv-x)))
        (list
         'equal
         (q9993851-static-apply-term
          add
          (list xy-add 'z))
         (q9993851-static-apply-term
          add
          (list 'x yz-add)))
        (list
         'equal
         xy-add
         (q9993851-static-apply-term add '(y x)))
        (list
         'equal
         (q9993851-static-apply-term
          add
          (list 'x (q9993851-quoted zero)))
         'x)
        (list
         'equal
         (q9993851-static-apply-term
          add
          (list 'x neg-x))
         (q9993851-quoted zero))
        (list
         'equal
         (q9993851-static-apply-term
          multiply
          (list xy-mul 'z))
         (q9993851-static-apply-term
          multiply
          (list 'x yz-mul)))
        (list
         'equal
         xy-mul
         (q9993851-static-apply-term multiply '(y x)))
        (list
         'equal
         (q9993851-static-apply-term
          multiply
          (list 'x (q9993851-quoted one)))
         'x)
        (q9993851-implies-term
         (q9993851-not-term
          (list 'equal 'x (q9993851-quoted zero)))
         (list
          'equal
          (q9993851-static-apply-term
           multiply
           (list 'x inv-x))
          (q9993851-quoted one)))
        (list
         'equal
         (q9993851-static-apply-term
          multiply
          (list 'x yz-add))
         (q9993851-static-apply-term
          add
          (list
           (q9993851-static-apply-term
            multiply '(x y))
           (q9993851-static-apply-term
            multiply '(x z)))))
        (q9993851-implies-term
         (q9993851-static-apply-term norm-lt '(x q))
         (list
          'q9993851-positive-rational-p
          'q))
        (q9993851-implies-term
         (q9993851-and-terms
          (list
           (q9993851-static-apply-term norm-lt '(x q))
           (list 'rationalp 'r)
           (list '< 'q 'r)))
         (q9993851-static-apply-term norm-lt '(x r)))
        (q9993851-implies-term
         (q9993851-static-apply-term norm-lt '(x q))
         (list
          'q9993851-rounded-p
          (q9993851-quoted norm-lt)
          'x
          'q))
        (list
         'q9993851-norm-finite-p
         (q9993851-quoted norm-lt)
         'x)
        (q9993851-implies-term
         (q9993851-not-term
          (list 'equal 'x (q9993851-quoted zero)))
         (list
          'q9993851-norm-positive-p
          (q9993851-quoted norm-lt)
          'x))
        (q9993851-implies-term
         (list 'q9993851-positive-rational-p 'q)
         (q9993851-static-apply-term
          norm-lt
          (list (q9993851-quoted zero) 'q)))
        (q9993851-iff-term
         (q9993851-static-apply-term
          norm-lt
          (list neg-x 'q))
         (q9993851-static-apply-term norm-lt '(x q)))
        (q9993851-implies-term
         (q9993851-and-terms
          (list
           (list 'q9993851-positive-rational-p 'r)
           (list 'q9993851-positive-rational-p 's)
           (q9993851-static-apply-term norm-lt '(x r))
           (q9993851-static-apply-term norm-lt '(y s))))
         (q9993851-static-apply-term
          norm-lt
          (list
           xy-add
           (list '+ 'r 's))))
        (q9993851-iff-term
         (q9993851-static-apply-term
          norm-lt
          (list xy-mul 'q))
         (list
          'q9993851-product-lt-p
          (q9993851-quoted norm-lt)
          'x
          'y
          'q))))))))

(defun q9993851-nontrivial-norm-witness-p
    (carrier norm-lt witness)
  (let ((x (car witness))
        (q (cdr witness)))
    (and
     (q9993851-member-p carrier x)
     (rationalp q)
     (< 1 q)
     (not (q9993851-norm-lt-p norm-lt x q)))))

(defun q9993851-nontrivial-norm-failure-function
    (carrier norm-lt)
  (list
   'lambda
   '(witness)
   (list
    'if
    (list
     'q9993851-nontrivial-norm-witness-p
     (q9993851-quoted carrier)
     (q9993851-quoted norm-lt)
     'witness)
    (q9993851-quoted nil)
    (q9993851-quoted t))))

(defun q9993851-nontrivial-norm-p
    (carrier norm-lt)
  (let ((failure
         (q9993851-nontrivial-norm-failure-function
          carrier norm-lt))
        (always-true
         (q9993851-true-function '(witness))))
    (and
     (tamep-functionp failure)
     (tamep-functionp always-true)
     (not (fn-equal failure always-true)))))

(defun q9993851-nontrivially-normed-field-p
    (carrier add multiply negate inverse zero one norm-lt)
  (let ((row
         (q9993851-field-row-function
          carrier add multiply negate inverse
          zero one norm-lt)))
    (and
     (tamep-functionp carrier)
     (tamep-functionp add)
     (tamep-functionp multiply)
     (tamep-functionp negate)
     (tamep-functionp inverse)
     (tamep-functionp norm-lt)
     (q9993851-member-p carrier zero)
     (q9993851-member-p carrier one)
     (not (equal zero one))
     (equal (apply$ inverse (list zero)) zero)
     (q9993851-fn-equal-true-p
      row '(x y z q r s))
     (q9993851-nontrivial-norm-p
      carrier norm-lt))))

(defun q9993851-space-row-function
    (field-carrier field-add field-multiply field-one field-norm-lt
     carrier add negate zero scalar-multiply norm-lt)
  (let* ((xy-add
          (q9993851-static-apply-term add '(x y)))
         (yz-add
          (q9993851-static-apply-term add '(y z)))
         (neg-x
          (q9993851-static-apply-term negate '(x)))
         (a-smul-x
          (q9993851-static-apply-term scalar-multiply '(a x))))
    (list
     'lambda
     '(a b x y z q r s)
     (q9993851-implies-term
      (q9993851-and-terms
       (list
        (q9993851-static-apply-term field-carrier '(a))
        (q9993851-static-apply-term field-carrier '(b))
        (q9993851-static-apply-term carrier '(x))
        (q9993851-static-apply-term carrier '(y))
        (q9993851-static-apply-term carrier '(z))))
      (q9993851-and-terms
       (list
        (q9993851-static-apply-term carrier
                                   (list xy-add))
        (q9993851-static-apply-term carrier
                                   (list neg-x))
        (q9993851-static-apply-term carrier
                                   (list a-smul-x))
        (list
         'equal
         (q9993851-static-apply-term
          add
          (list xy-add 'z))
         (q9993851-static-apply-term
          add
          (list 'x yz-add)))
        (list
         'equal
         xy-add
         (q9993851-static-apply-term add '(y x)))
        (list
         'equal
         (q9993851-static-apply-term
          add
          (list 'x (q9993851-quoted zero)))
         'x)
        (list
         'equal
         (q9993851-static-apply-term
          add
          (list 'x neg-x))
         (q9993851-quoted zero))
        (list
         'equal
         (q9993851-static-apply-term
          scalar-multiply
          (list
           (q9993851-quoted field-one)
           'x))
         'x)
        (list
         'equal
         (q9993851-static-apply-term
          scalar-multiply
          (list
           (q9993851-static-apply-term
            field-multiply '(a b))
           'x))
         (q9993851-static-apply-term
          scalar-multiply
          (list
           'a
           (q9993851-static-apply-term
            scalar-multiply '(b x)))))
        (list
         'equal
         (q9993851-static-apply-term
          scalar-multiply
          (list
           (q9993851-static-apply-term
            field-add '(a b))
           'x))
         (q9993851-static-apply-term
          add
          (list
           a-smul-x
           (q9993851-static-apply-term
            scalar-multiply '(b x)))))
        (list
         'equal
         (q9993851-static-apply-term
          scalar-multiply
          (list 'a xy-add))
         (q9993851-static-apply-term
          add
          (list
           a-smul-x
           (q9993851-static-apply-term
            scalar-multiply '(a y)))))
        (q9993851-implies-term
         (q9993851-static-apply-term norm-lt '(x q))
         (list
          'q9993851-positive-rational-p
          'q))
        (q9993851-implies-term
         (q9993851-and-terms
          (list
           (q9993851-static-apply-term norm-lt '(x q))
           (list 'rationalp 'r)
           (list '< 'q 'r)))
         (q9993851-static-apply-term norm-lt '(x r)))
        (q9993851-implies-term
         (q9993851-static-apply-term norm-lt '(x q))
         (list
          'q9993851-rounded-p
          (q9993851-quoted norm-lt)
          'x
          'q))
        (list
         'q9993851-norm-finite-p
         (q9993851-quoted norm-lt)
         'x)
        (q9993851-implies-term
         (q9993851-not-term
          (list 'equal 'x (q9993851-quoted zero)))
         (list
          'q9993851-norm-positive-p
          (q9993851-quoted norm-lt)
          'x))
        (q9993851-implies-term
         (list 'q9993851-positive-rational-p 'q)
         (q9993851-static-apply-term
          norm-lt
          (list (q9993851-quoted zero) 'q)))
        (q9993851-iff-term
         (q9993851-static-apply-term
          norm-lt
          (list neg-x 'q))
         (q9993851-static-apply-term norm-lt '(x q)))
        (q9993851-implies-term
         (q9993851-and-terms
          (list
           (list 'q9993851-positive-rational-p 'r)
           (list 'q9993851-positive-rational-p 's)
           (q9993851-static-apply-term norm-lt '(x r))
           (q9993851-static-apply-term norm-lt '(y s))))
         (q9993851-static-apply-term
          norm-lt
          (list
           xy-add
           (list '+ 'r 's))))
        (q9993851-iff-term
         (q9993851-static-apply-term
          norm-lt
          (list a-smul-x 'q))
         (list
          'q9993851-mixed-product-lt-p
          (q9993851-quoted field-norm-lt)
          (q9993851-quoted norm-lt)
          'a
          'x
          'q))))))))

(defun q9993851-sequence-valid-function
    (carrier sequence)
  (list
   'lambda
   '(n)
   (q9993851-implies-term
    (list 'natp 'n)
    (q9993851-static-apply-term
     carrier
     (list
      (q9993851-static-apply-term sequence '(n)))))))

(defun q9993851-sequence-valid-p
    (carrier sequence)
  (let ((law
         (q9993851-sequence-valid-function
          carrier sequence)))
    (and
     (tamep-functionp sequence)
     (q9993851-fn-equal-true-p law '(n)))))

(defun q9993851-norm-difference-lt-p
    (add negate norm-lt left right epsilon)
  (q9993851-norm-lt-p
   norm-lt
   (q9993851-binary-value
    add
    left
    (apply$ negate (list right)))
   epsilon))

(defun q9993851-cauchy-tail-function
    (add negate norm-lt sequence epsilon n0)
  (list
   'lambda
   '(m n)
   (q9993851-implies-term
    (q9993851-and-terms
     (list
      (list 'natp 'm)
      (list 'natp 'n)
      (list '<= (q9993851-quoted n0) 'm)
      (list '<= (q9993851-quoted n0) 'n)))
    (list
     'q9993851-norm-difference-lt-p
     (q9993851-quoted add)
     (q9993851-quoted negate)
     (q9993851-quoted norm-lt)
     (q9993851-static-apply-term sequence '(m))
     (q9993851-static-apply-term sequence '(n))
     (q9993851-quoted epsilon)))))

(defun q9993851-cauchy-tail-p
    (add negate norm-lt sequence epsilon n0)
  (and
   (natp n0)
   (q9993851-fn-equal-true-p
    (q9993851-cauchy-tail-function
     add negate norm-lt sequence epsilon n0)
    '(m n))))

(defun q9993851-cauchy-epsilon-failure-function
    (add negate norm-lt sequence epsilon)
  (list
   'lambda
   '(n0)
   (list
    'if
    (list
     'q9993851-cauchy-tail-p
     (q9993851-quoted add)
     (q9993851-quoted negate)
     (q9993851-quoted norm-lt)
     (q9993851-quoted sequence)
     (q9993851-quoted epsilon)
     'n0)
    (q9993851-quoted nil)
    (q9993851-quoted t))))

(defun q9993851-cauchy-epsilon-p
    (add negate norm-lt sequence epsilon)
  (let ((failure
         (q9993851-cauchy-epsilon-failure-function
          add negate norm-lt sequence epsilon))
        (always-true
         (q9993851-true-function '(n0))))
    (and
     (q9993851-positive-rational-p epsilon)
     (tamep-functionp failure)
     (tamep-functionp always-true)
     (not (fn-equal failure always-true)))))

(defun q9993851-cauchy-function
    (add negate norm-lt sequence)
  (list
   'lambda
   '(epsilon)
   (q9993851-implies-term
    (list 'q9993851-positive-rational-p 'epsilon)
    (list
     'q9993851-cauchy-epsilon-p
     (q9993851-quoted add)
     (q9993851-quoted negate)
     (q9993851-quoted norm-lt)
     (q9993851-quoted sequence)
     'epsilon))))

(defun q9993851-cauchy-p
    (carrier add negate norm-lt sequence)
  (and
   (q9993851-sequence-valid-p carrier sequence)
   (q9993851-fn-equal-true-p
    (q9993851-cauchy-function
     add negate norm-lt sequence)
    '(epsilon))))

(defun q9993851-convergence-tail-function
    (add negate norm-lt sequence limit epsilon n0)
  (list
   'lambda
   '(n)
   (q9993851-implies-term
    (q9993851-and-terms
     (list
      (list 'natp 'n)
      (list '<= (q9993851-quoted n0) 'n)))
    (list
     'q9993851-norm-difference-lt-p
     (q9993851-quoted add)
     (q9993851-quoted negate)
     (q9993851-quoted norm-lt)
     (q9993851-static-apply-term sequence '(n))
     (q9993851-quoted limit)
     (q9993851-quoted epsilon)))))

(defun q9993851-convergence-tail-p
    (add negate norm-lt sequence limit epsilon n0)
  (and
   (natp n0)
   (q9993851-fn-equal-true-p
    (q9993851-convergence-tail-function
     add negate norm-lt sequence limit epsilon n0)
    '(n))))

(defun q9993851-convergence-epsilon-failure-function
    (add negate norm-lt sequence limit epsilon)
  (list
   'lambda
   '(n0)
   (list
    'if
    (list
     'q9993851-convergence-tail-p
     (q9993851-quoted add)
     (q9993851-quoted negate)
     (q9993851-quoted norm-lt)
     (q9993851-quoted sequence)
     (q9993851-quoted limit)
     (q9993851-quoted epsilon)
     'n0)
    (q9993851-quoted nil)
    (q9993851-quoted t))))

(defun q9993851-convergence-epsilon-p
    (add negate norm-lt sequence limit epsilon)
  (let ((failure
         (q9993851-convergence-epsilon-failure-function
          add negate norm-lt sequence limit epsilon))
        (always-true
         (q9993851-true-function '(n0))))
    (and
     (q9993851-positive-rational-p epsilon)
     (tamep-functionp failure)
     (tamep-functionp always-true)
     (not (fn-equal failure always-true)))))

(defun q9993851-convergence-function
    (add negate norm-lt sequence limit)
  (list
   'lambda
   '(epsilon)
   (q9993851-implies-term
    (list 'q9993851-positive-rational-p 'epsilon)
    (list
     'q9993851-convergence-epsilon-p
     (q9993851-quoted add)
     (q9993851-quoted negate)
     (q9993851-quoted norm-lt)
     (q9993851-quoted sequence)
     (q9993851-quoted limit)
     'epsilon))))

(defun q9993851-converges-p
    (carrier add negate norm-lt sequence limit)
  (and
   (q9993851-member-p carrier limit)
   (q9993851-sequence-valid-p carrier sequence)
   (q9993851-fn-equal-true-p
    (q9993851-convergence-function
     add negate norm-lt sequence limit)
    '(epsilon))))

(defun q9993851-limit-witness-p
    (carrier add negate norm-lt sequence limit)
  (and
   (q9993851-member-p carrier limit)
   (q9993851-converges-p
    carrier add negate norm-lt sequence limit)))

(defun q9993851-limit-failure-function
    (carrier add negate norm-lt sequence)
  (list
   'lambda
   '(limit)
   (list
    'if
    (list
     'q9993851-limit-witness-p
     (q9993851-quoted carrier)
     (q9993851-quoted add)
     (q9993851-quoted negate)
     (q9993851-quoted norm-lt)
     (q9993851-quoted sequence)
     'limit)
    (q9993851-quoted nil)
    (q9993851-quoted t))))

(defun q9993851-limit-exists-p
    (carrier add negate norm-lt sequence)
  (let ((failure
         (q9993851-limit-failure-function
          carrier add negate norm-lt sequence))
        (always-true
         (q9993851-true-function '(limit))))
    (and
     (tamep-functionp failure)
     (tamep-functionp always-true)
     (not (fn-equal failure always-true)))))

(defun q9993851-completeness-function
    (carrier add negate norm-lt)
  (list
   'lambda
   '(sequence)
   (q9993851-implies-term
    (list
     'q9993851-cauchy-p
     (q9993851-quoted carrier)
     (q9993851-quoted add)
     (q9993851-quoted negate)
     (q9993851-quoted norm-lt)
     'sequence)
    (list
     'q9993851-limit-exists-p
     (q9993851-quoted carrier)
     (q9993851-quoted add)
     (q9993851-quoted negate)
     (q9993851-quoted norm-lt)
     'sequence))))

(defun q9993851-or-terms (terms)
  (if (consp terms)
      (list
       'if
       (car terms)
       (q9993851-quoted t)
       (q9993851-or-terms (cdr terms)))
    (q9993851-quoted nil)))

(defun q9993851-false-function (formals)
  (list 'lambda formals (q9993851-quoted nil)))

(defun q9993851-exists-p (function formals)
  (let ((always-false
         (q9993851-false-function formals)))
    (and
     (tamep-functionp function)
     (tamep-functionp always-false)
     (not (fn-equal function always-false)))))

;; Canonical rational casts into a presented field.

(defun q9993851-natural-cast (n zero one add)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      zero
    (q9993851-binary-value
     add one
     (q9993851-natural-cast (- n 1) zero one add))))

(defun q9993851-integer-cast
    (n zero one add negate)
  (if (and (integerp n) (< n 0))
      (apply$
       negate
       (list
        (q9993851-natural-cast
         (- n) zero one add)))
    (q9993851-natural-cast
     (nfix n) zero one add)))

(defun q9993851-rational-cast
    (q zero one add multiply negate inverse)
  (if (rationalp q)
      (q9993851-binary-value
       multiply
       (q9993851-integer-cast
        (numerator q) zero one add negate)
       (apply$
        inverse
        (list
         (q9993851-integer-cast
          (denominator q) zero one add negate))))
    zero))

;; A complete Archimedean ordered-field presentation of the real numbers.
;; Archimedeanness follows from the rationally finite absolute-value cuts.

(defun q9993851-order-laws-function
    (carrier zero add multiply less)
  (let ((xy (q9993851-static-apply-term less '(x y)))
        (yx (q9993851-static-apply-term less '(y x)))
        (yz (q9993851-static-apply-term less '(y z))))
    (list
     'lambda
     '(x y z)
     (q9993851-implies-term
      (q9993851-and-terms
       (list
        (q9993851-static-apply-term carrier '(x))
        (q9993851-static-apply-term carrier '(y))
        (q9993851-static-apply-term carrier '(z))))
      (q9993851-and-terms
       (list
        (q9993851-not-term
         (q9993851-static-apply-term less '(x x)))
        (q9993851-or-terms
         (list xy yx (list 'equal 'x 'y)))
        (q9993851-implies-term
         (q9993851-and-terms (list xy yz))
         (q9993851-static-apply-term less '(x z)))
        (q9993851-implies-term
         xy
         (q9993851-static-apply-term
          less
          (list
           (q9993851-static-apply-term add '(x z))
           (q9993851-static-apply-term add '(y z)))))
        (q9993851-implies-term
         (q9993851-and-terms
          (list
           (q9993851-static-apply-term
            less
            (list (q9993851-quoted zero) 'x))
           (q9993851-static-apply-term
            less
            (list (q9993851-quoted zero) 'y))))
         (q9993851-static-apply-term
          less
          (list
           (q9993851-quoted zero)
           (q9993851-static-apply-term
            multiply '(x y)))))))))))

(defun q9993851-real-norm-order-function
    (carrier zero one add multiply negate inverse less norm-lt)
  (let* ((cast-q
          (list
           'q9993851-rational-cast
           'q
           (q9993851-quoted zero)
           (q9993851-quoted one)
           (q9993851-quoted add)
           (q9993851-quoted multiply)
           (q9993851-quoted negate)
           (q9993851-quoted inverse)))
         (neg-cast-q
          (q9993851-static-apply-term
           negate
           (list cast-q))))
    (list
     'lambda
     '(x q)
     (q9993851-implies-term
      (q9993851-static-apply-term carrier '(x))
      (q9993851-iff-term
       (q9993851-static-apply-term norm-lt '(x q))
       (q9993851-and-terms
        (list
         (list 'q9993851-positive-rational-p 'q)
         (q9993851-static-apply-term less
                                    (list neg-cast-q 'x))
         (q9993851-static-apply-term less
                                    (list 'x cast-q)))))))))

(defun q9993851-normed-space-p
    (field-carrier field-add field-multiply field-one field-norm-lt
     carrier add negate zero scalar-multiply norm-lt)
  (let ((row
         (q9993851-space-row-function
          field-carrier field-add field-multiply
          field-one field-norm-lt
          carrier add negate zero scalar-multiply norm-lt)))
    (and
     (tamep-functionp carrier)
     (tamep-functionp add)
     (tamep-functionp negate)
     (tamep-functionp scalar-multiply)
     (tamep-functionp norm-lt)
     (q9993851-member-p carrier zero)
     (q9993851-fn-equal-true-p
      row '(a b x y z q r s)))))

(defun q9993851-banach-space-p
    (field-carrier field-add field-multiply field-one field-norm-lt
     carrier add negate zero scalar-multiply norm-lt)
  (and
   (q9993851-normed-space-p
    field-carrier field-add field-multiply field-one field-norm-lt
    carrier add negate zero scalar-multiply norm-lt)
   (q9993851-fn-equal-true-p
    (q9993851-completeness-function
     carrier add negate norm-lt)
    '(sequence))))

(defun q9993851-real-field-p
    (carrier add multiply negate inverse zero one less norm-lt)
  (and
   (q9993851-nontrivially-normed-field-p
    carrier add multiply negate inverse zero one norm-lt)
   (tamep-functionp less)
   (q9993851-fn-equal-true-p
    (q9993851-order-laws-function
     carrier zero add multiply less)
    '(x y z))
   (q9993851-binary-value less zero one)
   (q9993851-fn-equal-true-p
    (q9993851-real-norm-order-function
     carrier zero one add multiply negate inverse less norm-lt)
    '(x q))
   (q9993851-banach-space-p
    carrier add multiply one norm-lt
    carrier add negate zero multiply norm-lt)))

;; A real inner-product space. The norm cut is definitionally tied to
;; <x,x>, and the second argument of the inner product is linear, matching
;; the source convention.

(defun q9993851-inner-product-laws-function
    (real-carrier real-add real-multiply real-negate real-inverse
     real-zero real-one real-less
     carrier add zero smul norm-lt inner)
  (let* ((xy-inner
          (q9993851-static-apply-term inner '(x y)))
         (yx-inner
          (q9993851-static-apply-term inner '(y x)))
         (xx-inner
          (q9993851-static-apply-term inner '(x x)))
         (cast-q
          (list
           'q9993851-rational-cast
           'q
           (q9993851-quoted real-zero)
           (q9993851-quoted real-one)
           (q9993851-quoted real-add)
           (q9993851-quoted real-multiply)
           (q9993851-quoted real-negate)
           (q9993851-quoted real-inverse)))
         (q-square
          (q9993851-static-apply-term
           real-multiply
           (list cast-q cast-q))))
    (list
     'lambda
     '(a x y z q)
     (q9993851-implies-term
      (q9993851-and-terms
       (list
        (q9993851-static-apply-term real-carrier '(a))
        (q9993851-static-apply-term carrier '(x))
        (q9993851-static-apply-term carrier '(y))
        (q9993851-static-apply-term carrier '(z))))
      (q9993851-and-terms
       (list
        (q9993851-static-apply-term
         real-carrier
         (list xy-inner))
        (q9993851-static-apply-term
         real-carrier
         (list yx-inner))
        (q9993851-static-apply-term
         real-carrier
         (list xx-inner))
        (q9993851-static-apply-term
         real-carrier
         (list
          (q9993851-static-apply-term
           inner '(x z))))
        (list
         'equal
         (q9993851-static-apply-term
          inner
          (list
           'x
           (q9993851-static-apply-term add '(y z))))
         (q9993851-static-apply-term
          real-add
          (list
           xy-inner
           (q9993851-static-apply-term inner '(x z)))))
        (list
         'equal
         (q9993851-static-apply-term
          inner
          (list
           'x
           (q9993851-static-apply-term smul '(a y))))
         (q9993851-static-apply-term
          real-multiply
          (list 'a xy-inner)))
        (list 'equal yx-inner xy-inner)
        (q9993851-not-term
         (q9993851-static-apply-term
          real-less
          (list xx-inner
                (q9993851-quoted real-zero))))
        (q9993851-iff-term
         (list 'equal xx-inner
               (q9993851-quoted real-zero))
         (list 'equal 'x
               (q9993851-quoted zero)))
        (q9993851-iff-term
         (q9993851-static-apply-term norm-lt '(x q))
         (q9993851-and-terms
          (list
           (list 'q9993851-positive-rational-p 'q)
           (q9993851-static-apply-term
            real-less
            (list xx-inner q-square)))))))))))

(defun q9993851-inner-product-space-p
    (real-carrier real-add real-multiply real-negate real-inverse
     real-zero real-one real-less real-norm-lt
     carrier add negate zero smul norm-lt inner)
  (and
   (q9993851-normed-space-p
    real-carrier
    real-add real-multiply real-one real-norm-lt
    carrier add negate zero smul norm-lt)
   (tamep-functionp inner)
   (q9993851-fn-equal-true-p
    (q9993851-inner-product-laws-function
     real-carrier real-add real-multiply real-negate real-inverse
     real-zero real-one real-less
     carrier add zero smul norm-lt inner)
    '(a x y z q))))

;; The source space is complete as well as an inner-product space.

(defun q9993851-hilbert-space-p
    (real-carrier real-add real-multiply real-negate real-inverse
     real-zero real-one real-less real-norm-lt
     carrier add negate zero smul norm-lt inner)
  (and
   (q9993851-inner-product-space-p
    real-carrier real-add real-multiply real-negate real-inverse
    real-zero real-one real-less real-norm-lt
    carrier add negate zero smul norm-lt inner)
   (q9993851-fn-equal-true-p
    (q9993851-completeness-function
     carrier add negate norm-lt)
    '(sequence))))

;; Linear maps and sequential continuity.

(defun q9993851-linear-map-function
    (field-carrier domain-carrier codomain-carrier
     domain-add codomain-add domain-smul codomain-smul mapping)
  (list
   'lambda
   '(a x y)
   (q9993851-implies-term
    (q9993851-and-terms
     (list
      (q9993851-static-apply-term field-carrier '(a))
      (q9993851-static-apply-term domain-carrier '(x))
      (q9993851-static-apply-term domain-carrier '(y))))
    (q9993851-and-terms
     (list
      (q9993851-static-apply-term
       codomain-carrier
       (list
        (q9993851-static-apply-term mapping '(x))))
      (list
       'equal
       (q9993851-static-apply-term
        mapping
        (list
         (q9993851-static-apply-term domain-add '(x y))))
       (q9993851-static-apply-term
        codomain-add
        (list
         (q9993851-static-apply-term mapping '(x))
         (q9993851-static-apply-term mapping '(y)))))
      (list
       'equal
       (q9993851-static-apply-term
        mapping
        (list
         (q9993851-static-apply-term domain-smul '(a x))))
       (q9993851-static-apply-term
        codomain-smul
        (list
         'a
         (q9993851-static-apply-term mapping '(x))))))))))

(defun q9993851-linear-map-p
    (field-carrier domain-carrier codomain-carrier
     domain-add codomain-add domain-smul codomain-smul mapping)
  (and
   (tamep-functionp mapping)
   (q9993851-fn-equal-true-p
    (q9993851-linear-map-function
     field-carrier domain-carrier codomain-carrier
     domain-add codomain-add domain-smul codomain-smul mapping)
    '(a x y))))

(defun q9993851-compose-sequence
    (mapping sequence)
  (list
   'lambda
   '(n)
   (q9993851-static-apply-term
    mapping
    (list
     (q9993851-static-apply-term sequence '(n))))))

(defun q9993851-continuity-function
    (domain-carrier domain-add domain-negate domain-norm-lt
     codomain-carrier codomain-add codomain-negate codomain-norm-lt
     mapping)
  (list
   'lambda
   '(sequence x)
   (q9993851-implies-term
    (list
     'q9993851-converges-p
     (q9993851-quoted domain-carrier)
     (q9993851-quoted domain-add)
     (q9993851-quoted domain-negate)
     (q9993851-quoted domain-norm-lt)
     'sequence
     'x)
    (list
     'q9993851-converges-p
     (q9993851-quoted codomain-carrier)
     (q9993851-quoted codomain-add)
     (q9993851-quoted codomain-negate)
     (q9993851-quoted codomain-norm-lt)
     (list
      'q9993851-compose-sequence
      (q9993851-quoted mapping)
      'sequence)
     (q9993851-static-apply-term mapping '(x))))))

(defun q9993851-continuous-p
    (domain-carrier domain-add domain-negate domain-norm-lt
     codomain-carrier codomain-add codomain-negate codomain-norm-lt
     mapping)
  (q9993851-fn-equal-true-p
   (q9993851-continuity-function
    domain-carrier domain-add domain-negate domain-norm-lt
    codomain-carrier codomain-add codomain-negate codomain-norm-lt
    mapping)
   '(sequence x)))

(defun q9993851-continuous-linear-map-p
    (real-carrier
     carrier add negate smul norm-lt mapping)
  (and
   (q9993851-linear-map-p
    real-carrier carrier carrier
    add add smul smul mapping)
   (q9993851-continuous-p
    carrier add negate norm-lt
    carrier add negate norm-lt
    mapping)))

;; A bounded real bilinear form is represented as a bilinear map that is
;; jointly sequentially continuous.

(defun q9993851-bilinear-laws-function
    (real-carrier real-add real-multiply
     carrier add smul bilinear)
  (let ((bxy
         (q9993851-static-apply-term bilinear '(x y))))
    (list
     'lambda
     '(a x y z)
     (q9993851-implies-term
      (q9993851-and-terms
       (list
        (q9993851-static-apply-term real-carrier '(a))
        (q9993851-static-apply-term carrier '(x))
        (q9993851-static-apply-term carrier '(y))
        (q9993851-static-apply-term carrier '(z))))
      (q9993851-and-terms
       (list
        (q9993851-static-apply-term
         real-carrier
         (list bxy))
        (list
         'equal
         (q9993851-static-apply-term
          bilinear
          (list
           (q9993851-static-apply-term add '(x y))
           'z))
         (q9993851-static-apply-term
          real-add
          (list
           (q9993851-static-apply-term bilinear '(x z))
           (q9993851-static-apply-term bilinear '(y z)))))
        (list
         'equal
         (q9993851-static-apply-term
          bilinear
          (list
           (q9993851-static-apply-term smul '(a x))
           'z))
         (q9993851-static-apply-term
          real-multiply
          (list
           'a
           (q9993851-static-apply-term bilinear '(x z)))))
        (list
         'equal
         (q9993851-static-apply-term
          bilinear
          (list
           'x
           (q9993851-static-apply-term add '(y z))))
         (q9993851-static-apply-term
          real-add
          (list
           bxy
           (q9993851-static-apply-term bilinear '(x z)))))
        (list
         'equal
         (q9993851-static-apply-term
          bilinear
          (list
           'x
           (q9993851-static-apply-term smul '(a y))))
         (q9993851-static-apply-term
          real-multiply
          (list 'a bxy)))))))))

(defun q9993851-bilinear-map-p
    (real-carrier real-add real-multiply
     carrier add smul bilinear)
  (and
   (tamep-functionp bilinear)
   (q9993851-fn-equal-true-p
    (q9993851-bilinear-laws-function
     real-carrier real-add real-multiply
     carrier add smul bilinear)
    '(a x y z))))

(defun q9993851-compose-bilinear-sequence
    (bilinear left-sequence right-sequence)
  (list
   'lambda
   '(n)
   (q9993851-static-apply-term
    bilinear
    (list
     (q9993851-static-apply-term left-sequence '(n))
     (q9993851-static-apply-term right-sequence '(n))))))

(defun q9993851-bilinear-continuity-function
    (real-carrier real-add real-negate real-norm-lt
     carrier add negate norm-lt bilinear)
  (list
   'lambda
   '(left-sequence right-sequence left right)
   (q9993851-implies-term
    (q9993851-and-terms
     (list
      (list
       'q9993851-converges-p
       (q9993851-quoted carrier)
       (q9993851-quoted add)
       (q9993851-quoted negate)
       (q9993851-quoted norm-lt)
       'left-sequence
       'left)
      (list
       'q9993851-converges-p
       (q9993851-quoted carrier)
       (q9993851-quoted add)
       (q9993851-quoted negate)
       (q9993851-quoted norm-lt)
       'right-sequence
       'right)))
    (list
     'q9993851-converges-p
     (q9993851-quoted real-carrier)
     (q9993851-quoted real-add)
     (q9993851-quoted real-negate)
     (q9993851-quoted real-norm-lt)
     (list
      'q9993851-compose-bilinear-sequence
      (q9993851-quoted bilinear)
      'left-sequence
      'right-sequence)
     (q9993851-static-apply-term
      bilinear '(left right))))))

(defun q9993851-bounded-bilinear-form-p
    (real-carrier real-add real-multiply real-negate real-norm-lt
     carrier add negate smul norm-lt bilinear)
  (and
   (q9993851-bilinear-map-p
    real-carrier real-add real-multiply
    carrier add smul bilinear)
   (q9993851-fn-equal-true-p
    (q9993851-bilinear-continuity-function
     real-carrier real-add real-negate real-norm-lt
     carrier add negate norm-lt bilinear)
    '(left-sequence right-sequence left right))))

;; Coercivity. The rational witness remains existential inside the predicate.

(defun q9993851-real-le-p
    (real-less left right)
  (not (q9993851-binary-value
        real-less right left)))

(defun q9993851-coercivity-row-function
    (real-add real-multiply real-negate real-inverse
     real-zero real-one real-less
     carrier inner bilinear constant)
  (let* ((cast-constant
          (list
           'q9993851-rational-cast
           (q9993851-quoted constant)
           (q9993851-quoted real-zero)
           (q9993851-quoted real-one)
           (q9993851-quoted real-add)
           (q9993851-quoted real-multiply)
           (q9993851-quoted real-negate)
           (q9993851-quoted real-inverse)))
         (scaled-square
          (q9993851-static-apply-term
           real-multiply
           (list
            cast-constant
            (q9993851-static-apply-term inner '(u u))))))
    (list
     'lambda
     '(u)
     (q9993851-implies-term
      (q9993851-static-apply-term carrier '(u))
      (list
       'q9993851-real-le-p
       (q9993851-quoted real-less)
       scaled-square
       (q9993851-static-apply-term bilinear '(u u)))))))

(defun q9993851-coercivity-witness-p
    (real-add real-multiply real-negate real-inverse
     real-zero real-one real-less
     carrier inner bilinear constant)
  (and
   (q9993851-positive-rational-p constant)
   (q9993851-fn-equal-true-p
    (q9993851-coercivity-row-function
     real-add real-multiply real-negate real-inverse
     real-zero real-one real-less
     carrier inner bilinear constant)
    '(u))))

(defun q9993851-coercivity-witness-function
    (real-add real-multiply real-negate real-inverse
     real-zero real-one real-less
     carrier inner bilinear)
  (list
   'lambda
   '(constant)
   (list
    'q9993851-coercivity-witness-p
    (q9993851-quoted real-add)
    (q9993851-quoted real-multiply)
    (q9993851-quoted real-negate)
    (q9993851-quoted real-inverse)
    (q9993851-quoted real-zero)
    (q9993851-quoted real-one)
    (q9993851-quoted real-less)
    (q9993851-quoted carrier)
    (q9993851-quoted inner)
    (q9993851-quoted bilinear)
    'constant)))

(defun q9993851-coercive-p
    (real-add real-multiply real-negate real-inverse
     real-zero real-one real-less
     carrier inner bilinear)
  (q9993851-exists-p
   (q9993851-coercivity-witness-function
    real-add real-multiply real-negate real-inverse
    real-zero real-one real-less
    carrier inner bilinear)
   '(constant)))

;; A continuous linear equivalence whose forward map is the Riesz
;; representative of v |-> B(v,-).

(defun q9993851-equivalence-laws-function
    (carrier forward inverse)
  (list
   'lambda
   '(x)
   (q9993851-implies-term
    (q9993851-static-apply-term carrier '(x))
    (q9993851-and-terms
     (list
      (list
       'equal
       (q9993851-static-apply-term
        inverse
        (list
         (q9993851-static-apply-term forward '(x))))
       'x)
      (list
       'equal
       (q9993851-static-apply-term
        forward
        (list
         (q9993851-static-apply-term inverse '(x))))
       'x))))))

(defun q9993851-representation-function
    (carrier inner bilinear forward)
  (list
   'lambda
   '(v w)
   (q9993851-implies-term
    (q9993851-and-terms
     (list
      (q9993851-static-apply-term carrier '(v))
      (q9993851-static-apply-term carrier '(w))))
    (list
     'equal
     (q9993851-static-apply-term
      inner
      (list
       (q9993851-static-apply-term forward '(v))
       'w))
     (q9993851-static-apply-term bilinear '(v w))))))

(defun q9993851-equivalence-witness-p
    (real-carrier
     carrier add negate smul norm-lt
     inner bilinear witness)
  (let ((forward (nth 0 witness))
        (inverse (nth 1 witness)))
    (and
     (true-listp witness)
     (equal (len witness) 2)
     (q9993851-continuous-linear-map-p
      real-carrier
      carrier add negate smul norm-lt forward)
     (q9993851-continuous-linear-map-p
      real-carrier
      carrier add negate smul norm-lt inverse)
     (q9993851-fn-equal-true-p
      (q9993851-equivalence-laws-function
       carrier forward inverse)
      '(x))
     (q9993851-fn-equal-true-p
      (q9993851-representation-function
       carrier inner bilinear forward)
      '(v w)))))

(defun q9993851-equivalence-witness-function
    (real-carrier
     carrier add negate smul norm-lt inner bilinear)
  (list
   'lambda
   '(witness)
   (list
    'q9993851-equivalence-witness-p
    (q9993851-quoted real-carrier)
    (q9993851-quoted carrier)
    (q9993851-quoted add)
    (q9993851-quoted negate)
    (q9993851-quoted smul)
    (q9993851-quoted norm-lt)
    (q9993851-quoted inner)
    (q9993851-quoted bilinear)
    'witness)))

(defun q9993851-has-lax-milgram-equivalence-p
    (real-carrier
     carrier add negate smul norm-lt inner bilinear)
  (q9993851-exists-p
   (q9993851-equivalence-witness-function
    real-carrier
    carrier add negate smul norm-lt inner bilinear)
   '(witness)))

(defun thousand-theorems-q9993851-lax-milgram-theorem-statement
    (real-carrier real-add real-multiply real-negate real-inverse
     real-zero real-one real-less real-norm-lt
     carrier add negate zero smul norm-lt inner bilinear)
  (implies
   (and
    (q9993851-real-field-p
     real-carrier real-add real-multiply real-negate real-inverse
     real-zero real-one real-less real-norm-lt)
    (q9993851-hilbert-space-p
     real-carrier real-add real-multiply real-negate real-inverse
     real-zero real-one real-less real-norm-lt
     carrier add negate zero smul norm-lt inner)
    (q9993851-bounded-bilinear-form-p
     real-carrier real-add real-multiply real-negate real-norm-lt
     carrier add negate smul norm-lt bilinear)
    (q9993851-coercive-p
     real-add real-multiply real-negate real-inverse
     real-zero real-one real-less
     carrier inner bilinear))
   (q9993851-has-lax-milgram-equivalence-p
    real-carrier
    carrier add negate smul norm-lt inner bilinear)))

(value-triple :itpeval-statement-checked)
:q
