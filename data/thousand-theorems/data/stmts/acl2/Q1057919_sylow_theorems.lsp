;; Statement-only formalization of thousand-theorems corpus artifact Q1057919,
;; "Sylow theorems": existence of subgroups of prime-power order in finite
;; groups, conjugacy of Sylow subgroups when their type is finite, divisibility
;; of a Sylow subgroup's index by their number, and the congruence of that
;; number to one modulo the prime. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Arbitrary carriers, operations, and subgroups are represented by tame
;; function objects.  FN-EQUAL supplies unbounded universal quantification
;; over ACL2 objects, and inequality with an always-true function supplies
;; internal existential quantification.  Lists occur only as complete
;; enumerations where the Lean source has a Finite hypothesis.

(defun q1057919-quoted (object)
  (list 'quote object))

(defun q1057919-term-list (terms)
  (if (consp terms)
      (list
       'cons
       (car terms)
       (q1057919-term-list (cdr terms)))
    (q1057919-quoted nil)))

(defun q1057919-apply-term (function-term arguments)
  (list
   'apply$
   function-term
   (q1057919-term-list arguments)))

(defun q1057919-static-apply-term (function arguments)
  (q1057919-apply-term
   (q1057919-quoted function)
   arguments))

(defun q1057919-and-terms (terms)
  (if (consp terms)
      (list
       'if
       (car terms)
       (q1057919-and-terms (cdr terms))
       (q1057919-quoted nil))
    (q1057919-quoted t)))

(defun q1057919-implies-term (hypothesis conclusion)
  (list
   'if
   hypothesis
   conclusion
   (q1057919-quoted t)))

(defun q1057919-iff-term (left right)
  (list
   'if
   left
   (list
    'if
    right
    (q1057919-quoted t)
    (q1057919-quoted nil))
   (list
    'if
    right
    (q1057919-quoted nil)
    (q1057919-quoted t))))

(defun q1057919-true-function (formals)
  (list 'lambda formals (q1057919-quoted t)))

(defun q1057919-member-p (predicate object)
  (if (apply$ predicate (list object))
      t
    nil))

(defun q1057919-mul (multiplication left right)
  (apply$ multiplication (list left right)))

(defun q1057919-inv (inverse object)
  (apply$ inverse (list object)))

(defun q1057919-mul-term (multiplication left right)
  (q1057919-static-apply-term
   multiplication
   (list left right)))

(defun q1057919-inv-term (inverse object)
  (q1057919-static-apply-term inverse (list object)))

(defun q1057919-set-subset-function
    (carrier left right)
  (declare (ignore carrier))
  (list
   'lambda
   '(x)
   (q1057919-implies-term
    (q1057919-static-apply-term left '(x))
    (q1057919-static-apply-term right '(x)))))

(defun q1057919-set-subset-p
    (carrier left right)
  (let ((condition
         (q1057919-set-subset-function
          carrier left right))
        (always-true
         (q1057919-true-function '(x))))
    (and
     (tamep-functionp carrier)
     (tamep-functionp left)
     (tamep-functionp right)
     (tamep-functionp condition)
     (tamep-functionp always-true)
     (fn-equal condition always-true))))

(defun q1057919-valid-set-p (carrier set)
  (and
   (tamep-functionp carrier)
   (tamep-functionp set)
   (q1057919-set-subset-p carrier set carrier)))

(defun q1057919-set-equiv-function
    (carrier left right)
  (list
   'lambda
   '(x)
   (q1057919-implies-term
    (q1057919-static-apply-term carrier '(x))
    (q1057919-iff-term
     (q1057919-static-apply-term left '(x))
     (q1057919-static-apply-term right '(x))))))

(defun q1057919-set-equiv-p
    (carrier left right)
  (let ((condition
         (q1057919-set-equiv-function
          carrier left right))
        (always-true
         (q1057919-true-function '(x))))
    (and
     (q1057919-valid-set-p carrier left)
     (q1057919-valid-set-p carrier right)
     (tamep-functionp condition)
     (tamep-functionp always-true)
     (fn-equal condition always-true))))

(defun q1057919-group-row-function
    (carrier multiplication left)
  (list
   'lambda
   '(right)
   (q1057919-implies-term
    (q1057919-static-apply-term carrier '(right))
    (q1057919-static-apply-term
     carrier
     (list
      (q1057919-mul-term
       multiplication
       (q1057919-quoted left)
       'right))))))

(defun q1057919-group-row-closed-p
    (carrier multiplication left)
  (let ((condition
         (q1057919-group-row-function
          carrier multiplication left))
        (always-true
         (q1057919-true-function '(right))))
    (and
     (tamep-functionp condition)
     (tamep-functionp always-true)
     (fn-equal condition always-true))))

(defun q1057919-associative-third-function
    (carrier multiplication left middle)
  (list
   'lambda
   '(right)
   (q1057919-implies-term
    (q1057919-static-apply-term carrier '(right))
    (list
     'equal
     (q1057919-mul-term
      multiplication
      (q1057919-quoted left)
      (q1057919-mul-term
       multiplication
       (q1057919-quoted middle)
       'right))
     (q1057919-mul-term
      multiplication
      (q1057919-mul-term
       multiplication
       (q1057919-quoted left)
       (q1057919-quoted middle))
      'right)))))

(defun q1057919-associative-third-p
    (carrier multiplication left middle)
  (let ((condition
         (q1057919-associative-third-function
          carrier multiplication left middle))
        (always-true
         (q1057919-true-function '(right))))
    (and
     (tamep-functionp condition)
     (tamep-functionp always-true)
     (fn-equal condition always-true))))

(defun q1057919-associative-second-function
    (carrier multiplication left)
  (list
   'lambda
   '(middle)
   (q1057919-implies-term
    (q1057919-static-apply-term carrier '(middle))
    (list
     'q1057919-associative-third-p
     (q1057919-quoted carrier)
     (q1057919-quoted multiplication)
     (q1057919-quoted left)
     'middle))))

(defun q1057919-associative-second-p
    (carrier multiplication left)
  (let ((condition
         (q1057919-associative-second-function
          carrier multiplication left))
        (always-true
         (q1057919-true-function '(middle))))
    (and
     (tamep-functionp condition)
     (tamep-functionp always-true)
     (fn-equal condition always-true))))

(defun q1057919-group-element-laws-function
    (carrier multiplication inverse identity)
  (list
   'lambda
   '(x)
   (q1057919-implies-term
    (q1057919-static-apply-term carrier '(x))
    (q1057919-and-terms
     (list
      (q1057919-static-apply-term
       carrier
       (list (q1057919-inv-term inverse 'x)))
      (list
       'equal
       (q1057919-mul-term
        multiplication 'x (q1057919-quoted identity))
       'x)
      (list
       'equal
       (q1057919-mul-term
        multiplication (q1057919-quoted identity) 'x)
       'x)
      (list
       'equal
       (q1057919-mul-term
        multiplication
        'x
        (q1057919-inv-term inverse 'x))
       (q1057919-quoted identity))
      (list
       'equal
       (q1057919-mul-term
        multiplication
        (q1057919-inv-term inverse 'x)
        'x)
       (q1057919-quoted identity))
      (list
       'q1057919-group-row-closed-p
       (q1057919-quoted carrier)
       (q1057919-quoted multiplication)
       'x)
      (list
       'q1057919-associative-second-p
       (q1057919-quoted carrier)
       (q1057919-quoted multiplication)
       'x))))))

(defun q1057919-group-p
    (carrier multiplication inverse identity)
  (let ((condition
         (q1057919-group-element-laws-function
          carrier multiplication inverse identity))
        (always-true
         (q1057919-true-function '(x))))
    (and
     (tamep-functionp carrier)
     (tamep-functionp multiplication)
     (tamep-functionp inverse)
     (q1057919-member-p carrier identity)
     (tamep-functionp condition)
     (tamep-functionp always-true)
     (fn-equal condition always-true))))

(defun q1057919-subgroup-p
    (carrier multiplication inverse identity subgroup)
  (and
   (q1057919-group-p
    carrier multiplication inverse identity)
   (q1057919-set-subset-p
    carrier subgroup carrier)
   (q1057919-group-p
    subgroup multiplication inverse identity)))

(defun q1057919-power
    (multiplication identity x exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      identity
    (q1057919-mul
     multiplication
     x
     (q1057919-power
      multiplication identity x (- exponent 1)))))

(defun q1057919-p-power-witness-p
    (multiplication identity p x exponent)
  (and
   (natp exponent)
   (equal
    (q1057919-power
     multiplication
     identity
     x
     (expt p exponent))
    identity)))

(defun q1057919-p-power-failure-function
    (multiplication identity p x)
  (list
   'lambda
   '(exponent)
   (list
    'if
    (list
     'q1057919-p-power-witness-p
     (q1057919-quoted multiplication)
     (q1057919-quoted identity)
     (q1057919-quoted p)
     (q1057919-quoted x)
     'exponent)
    (q1057919-quoted nil)
    (q1057919-quoted t))))

(defun q1057919-p-element-p
    (multiplication identity p x)
  (let ((failure
         (q1057919-p-power-failure-function
          multiplication identity p x))
        (always-true
         (q1057919-true-function '(exponent))))
    (and
     (tamep-functionp failure)
     (tamep-functionp always-true)
     (not (fn-equal failure always-true)))))

(defun q1057919-p-group-elements-function
    (subgroup multiplication identity p)
  (list
   'lambda
   '(x)
   (q1057919-implies-term
    (q1057919-static-apply-term subgroup '(x))
    (list
     'q1057919-p-element-p
     (q1057919-quoted multiplication)
     (q1057919-quoted identity)
     (q1057919-quoted p)
     'x))))

(defun q1057919-p-group-p
    (carrier multiplication inverse identity p subgroup)
  (let ((condition
         (q1057919-p-group-elements-function
          subgroup multiplication identity p))
        (always-true
         (q1057919-true-function '(x))))
    (and
     (q1057919-subgroup-p
      carrier multiplication inverse identity subgroup)
     (tamep-functionp condition)
     (tamep-functionp always-true)
     (fn-equal condition always-true))))

(defun q1057919-sylow-maximal-function
    (carrier multiplication inverse identity p subgroup)
  (list
   'lambda
   '(larger)
   (q1057919-implies-term
    (q1057919-and-terms
     (list
      (list
       'q1057919-p-group-p
       (q1057919-quoted carrier)
       (q1057919-quoted multiplication)
       (q1057919-quoted inverse)
       (q1057919-quoted identity)
       (q1057919-quoted p)
       'larger)
      (list
       'q1057919-set-subset-p
       (q1057919-quoted carrier)
       (q1057919-quoted subgroup)
       'larger)))
    (list
     'q1057919-set-subset-p
     (q1057919-quoted carrier)
     'larger
     (q1057919-quoted subgroup)))))

(defun q1057919-sylow-p
    (carrier multiplication inverse identity p subgroup)
  (let ((condition
         (q1057919-sylow-maximal-function
          carrier multiplication inverse identity p subgroup))
        (always-true
         (q1057919-true-function '(larger))))
    (and
     (q1057919-p-group-p
      carrier multiplication inverse identity p subgroup)
     (tamep-functionp condition)
     (tamep-functionp always-true)
     (fn-equal condition always-true))))

(defun q1057919-list-has-equiv-set-p
    (carrier set sets)
  (if (atom sets)
      nil
    (or
     (q1057919-set-equiv-p carrier set (car sets))
     (q1057919-list-has-equiv-set-p
      carrier set (cdr sets)))))

(defun q1057919-sylow-list-elements-p
    (carrier multiplication inverse identity p sylows)
  (if (atom sylows)
      t
    (and
     (q1057919-sylow-p
      carrier
      multiplication
      inverse
      identity
      p
      (car sylows))
     (q1057919-sylow-list-elements-p
      carrier
      multiplication
      inverse
      identity
      p
      (cdr sylows)))))

(defun q1057919-sylow-list-no-duplicates-p
    (carrier sylows)
  (if (atom sylows)
      t
    (and
     (not
      (q1057919-list-has-equiv-set-p
       carrier (car sylows) (cdr sylows)))
     (q1057919-sylow-list-no-duplicates-p
      carrier (cdr sylows)))))

(defun q1057919-sylow-list-complete-function
    (carrier multiplication inverse identity p sylows)
  (list
   'lambda
   '(subgroup)
   (q1057919-implies-term
    (list
     'q1057919-sylow-p
     (q1057919-quoted carrier)
     (q1057919-quoted multiplication)
     (q1057919-quoted inverse)
     (q1057919-quoted identity)
     (q1057919-quoted p)
     'subgroup)
    (list
     'q1057919-list-has-equiv-set-p
     (q1057919-quoted carrier)
     'subgroup
     (q1057919-quoted sylows)))))

(defun q1057919-finite-sylow-enumeration-p
    (carrier multiplication inverse identity p sylows)
  (let ((condition
         (q1057919-sylow-list-complete-function
          carrier multiplication inverse identity p sylows))
        (always-true
         (q1057919-true-function '(subgroup))))
    (and
     (true-listp sylows)
     (consp sylows)
     (q1057919-sylow-list-elements-p
      carrier multiplication inverse identity p sylows)
     (q1057919-sylow-list-no-duplicates-p
      carrier sylows)
     (tamep-functionp condition)
     (tamep-functionp always-true)
     (fn-equal condition always-true))))

(defun q1057919-conjugate-set
    (carrier multiplication inverse subgroup conjugator)
  (list
   'lambda
   '(x)
   (q1057919-and-terms
    (list
     (q1057919-static-apply-term carrier '(x))
     (q1057919-static-apply-term
      subgroup
      (list
       (q1057919-mul-term
        multiplication
        (q1057919-mul-term
         multiplication
         (q1057919-inv-term
          inverse
          (q1057919-quoted conjugator))
         'x)
        (q1057919-quoted conjugator))))))))

(defun q1057919-conjugates-p
    (carrier multiplication inverse left right conjugator)
  (let ((conjugate
         (q1057919-conjugate-set
          carrier multiplication inverse left conjugator)))
    (and
     (q1057919-member-p carrier conjugator)
     (tamep-functionp conjugate)
     (q1057919-set-equiv-p
      carrier conjugate right))))

(defun q1057919-conjugator-failure-function
    (carrier multiplication inverse left right)
  (list
   'lambda
   '(conjugator)
   (list
    'if
    (list
     'q1057919-conjugates-p
     (q1057919-quoted carrier)
     (q1057919-quoted multiplication)
     (q1057919-quoted inverse)
     (q1057919-quoted left)
     (q1057919-quoted right)
     'conjugator)
    (q1057919-quoted nil)
    (q1057919-quoted t))))

(defun q1057919-conjugator-exists-p
    (carrier multiplication inverse left right)
  (let ((failure
         (q1057919-conjugator-failure-function
          carrier multiplication inverse left right))
        (always-true
         (q1057919-true-function '(conjugator))))
    (and
     (tamep-functionp failure)
     (tamep-functionp always-true)
     (not (fn-equal failure always-true)))))

(defun q1057919-conjugate-row-p
    (carrier multiplication inverse left sylows)
  (if (atom sylows)
      t
    (and
     (q1057919-conjugator-exists-p
      carrier multiplication inverse left (car sylows))
     (q1057919-conjugate-row-p
      carrier multiplication inverse left (cdr sylows)))))

(defun q1057919-all-sylows-conjugate-aux
    (carrier multiplication inverse remaining sylows)
  (if (atom remaining)
      t
    (and
     (q1057919-conjugate-row-p
      carrier multiplication inverse (car remaining) sylows)
     (q1057919-all-sylows-conjugate-aux
      carrier
      multiplication
      inverse
      (cdr remaining)
      sylows))))

(defun q1057919-all-sylows-conjugate-p
    (carrier multiplication inverse sylows)
  (q1057919-all-sylows-conjugate-aux
   carrier multiplication inverse sylows sylows))

(defun q1057919-enumerates-carrier-function
    (carrier elements)
  (list
   'lambda
   '(x)
   (q1057919-iff-term
    (q1057919-static-apply-term carrier '(x))
    (list
     'member-equal
     'x
     (q1057919-quoted elements)))))

(defun q1057919-finite-carrier-enumeration-p
    (carrier elements)
  (let ((condition
         (q1057919-enumerates-carrier-function
          carrier elements))
        (always-true
         (q1057919-true-function '(x))))
    (and
     (true-listp elements)
     (no-duplicatesp-equal elements)
     (tamep-functionp condition)
     (tamep-functionp always-true)
     (fn-equal condition always-true))))

(defun q1057919-subsetp-equal (left right)
  (if (atom left)
      t
    (and
     (member-equal (car left) right)
     (q1057919-subsetp-equal
      (cdr left) right))))

(defun q1057919-list-product-row-closed-p
    (left rights subgroup multiplication)
  (if (atom rights)
      t
    (and
     (member-equal
      (q1057919-mul
       multiplication left (car rights))
      subgroup)
     (q1057919-list-product-row-closed-p
      left (cdr rights) subgroup multiplication))))

(defun q1057919-list-product-closed-p
    (elements subgroup multiplication)
  (if (atom elements)
      t
    (and
     (q1057919-list-product-row-closed-p
      (car elements) subgroup subgroup multiplication)
     (q1057919-list-product-closed-p
      (cdr elements) subgroup multiplication))))

(defun q1057919-list-inverse-closed-p
    (elements subgroup inverse)
  (if (atom elements)
      t
    (and
     (member-equal
      (q1057919-inv inverse (car elements))
      subgroup)
     (q1057919-list-inverse-closed-p
      (cdr elements) subgroup inverse))))

(defun q1057919-list-subgroup-p
    (subgroup carrier-elements multiplication inverse identity)
  (and
   (true-listp subgroup)
   (no-duplicatesp-equal subgroup)
   (q1057919-subsetp-equal
    subgroup carrier-elements)
   (member-equal identity subgroup)
   (q1057919-list-product-closed-p
    subgroup subgroup multiplication)
   (q1057919-list-inverse-closed-p
    subgroup subgroup inverse)))

(defun q1057919-has-subgroup-of-order-p
    (remaining chosen carrier-elements multiplication inverse identity order)
  (if (atom remaining)
      (and
       (equal (len chosen) order)
       (q1057919-list-subgroup-p
        chosen
        carrier-elements
        multiplication
        inverse
        identity))
    (or
     (q1057919-has-subgroup-of-order-p
      (cdr remaining)
      (cons (car remaining) chosen)
      carrier-elements
      multiplication
      inverse
      identity
      order)
     (q1057919-has-subgroup-of-order-p
      (cdr remaining)
      chosen
      carrier-elements
      multiplication
      inverse
      identity
      order))))

(defun q1057919-no-divisor-from-p (n divisor)
  (declare (xargs :measure (nfix (- n divisor))))
  (if (and
       (natp n)
       (natp divisor)
       (<= 2 divisor)
       (< divisor n))
      (and
       (not (equal (mod n divisor) 0))
       (q1057919-no-divisor-from-p
        n (+ divisor 1)))
    t))

(defun q1057919-primep (n)
  (and
   (natp n)
   (< 1 n)
   (q1057919-no-divisor-from-p n 2)))

(defun q1057919-divides-p (divisor number)
  (and
   (natp divisor)
   (natp number)
   (if (equal divisor 0)
       (equal number 0)
     (equal (mod number divisor) 0))))

(defun q1057919-same-left-coset-p
    (subgroup multiplication inverse left right)
  (q1057919-member-p
   subgroup
   (q1057919-mul
    multiplication
    (q1057919-inv inverse left)
    right)))

(defun q1057919-list-has-coset-representative-p
    (subgroup multiplication inverse object representatives)
  (if (atom representatives)
      nil
    (or
     (q1057919-same-left-coset-p
      subgroup
      multiplication
      inverse
      (car representatives)
      object)
     (q1057919-list-has-coset-representative-p
      subgroup
      multiplication
      inverse
      object
      (cdr representatives)))))

(defun q1057919-representatives-in-carrier-p
    (carrier representatives)
  (if (atom representatives)
      t
    (and
     (q1057919-member-p carrier (car representatives))
     (q1057919-representatives-in-carrier-p
      carrier (cdr representatives)))))

(defun q1057919-coset-representatives-distinct-p
    (subgroup multiplication inverse representatives)
  (if (atom representatives)
      t
    (and
     (not
      (q1057919-list-has-coset-representative-p
       subgroup
       multiplication
       inverse
       (car representatives)
       (cdr representatives)))
     (q1057919-coset-representatives-distinct-p
      subgroup
      multiplication
      inverse
      (cdr representatives)))))

(defun q1057919-coset-representatives-complete-function
    (carrier subgroup multiplication inverse representatives)
  (list
   'lambda
   '(x)
   (q1057919-implies-term
    (q1057919-static-apply-term carrier '(x))
    (list
     'q1057919-list-has-coset-representative-p
     (q1057919-quoted subgroup)
     (q1057919-quoted multiplication)
     (q1057919-quoted inverse)
     'x
     (q1057919-quoted representatives)))))

(defun q1057919-coset-representatives-p
    (carrier subgroup multiplication inverse representatives)
  (let ((condition
         (q1057919-coset-representatives-complete-function
          carrier
          subgroup
          multiplication
          inverse
          representatives))
        (always-true
         (q1057919-true-function '(x))))
    (and
     (true-listp representatives)
     (q1057919-representatives-in-carrier-p
      carrier representatives)
     (q1057919-coset-representatives-distinct-p
      subgroup multiplication inverse representatives)
     (tamep-functionp condition)
     (tamep-functionp always-true)
     (fn-equal condition always-true))))

(defun q1057919-finite-index-failure-function
    (carrier subgroup multiplication inverse)
  (list
   'lambda
   '(representatives)
   (list
    'if
    (list
     'q1057919-coset-representatives-p
     (q1057919-quoted carrier)
     (q1057919-quoted subgroup)
     (q1057919-quoted multiplication)
     (q1057919-quoted inverse)
     'representatives)
    (q1057919-quoted nil)
    (q1057919-quoted t))))

(defun q1057919-finite-index-p
    (carrier subgroup multiplication inverse)
  (let ((failure
         (q1057919-finite-index-failure-function
          carrier subgroup multiplication inverse))
        (always-true
         (q1057919-true-function '(representatives))))
    (and
     (tamep-functionp failure)
     (tamep-functionp always-true)
     (not (fn-equal failure always-true)))))

(defun q1057919-exact-index-failure-function
    (carrier subgroup multiplication inverse index)
  (list
   'lambda
   '(representatives)
   (list
    'if
    (q1057919-and-terms
     (list
      (list
       'equal
       (list 'len 'representatives)
       (q1057919-quoted index))
      (list
       'q1057919-coset-representatives-p
       (q1057919-quoted carrier)
       (q1057919-quoted subgroup)
       (q1057919-quoted multiplication)
       (q1057919-quoted inverse)
       'representatives)))
    (q1057919-quoted nil)
    (q1057919-quoted t))))

(defun q1057919-exact-index-p
    (carrier subgroup multiplication inverse index)
  (let ((failure
         (q1057919-exact-index-failure-function
          carrier subgroup multiplication inverse index))
        (always-true
         (q1057919-true-function '(representatives))))
    (and
     (tamep-functionp failure)
     (tamep-functionp always-true)
     (not (fn-equal failure always-true)))))

(defun q1057919-subgroup-index-p
    (carrier subgroup multiplication inverse index)
  (and
   (natp index)
   (if (equal index 0)
       (not
        (q1057919-finite-index-p
         carrier subgroup multiplication inverse))
     (q1057919-exact-index-p
      carrier subgroup multiplication inverse index))))

(defun thousand-theorems-q1057919-exists-subgroup-card-pow-prime-statement
    (carrier
     carrier-elements
     multiplication
     inverse
     identity
     p
     exponent)
  (implies
   (and
    (q1057919-group-p
     carrier multiplication inverse identity)
    (q1057919-finite-carrier-enumeration-p
     carrier carrier-elements)
    (q1057919-primep p)
    (natp exponent)
    (q1057919-divides-p
     (expt p exponent)
     (len carrier-elements)))
   (q1057919-has-subgroup-of-order-p
    carrier-elements
    nil
    carrier-elements
    multiplication
    inverse
    identity
    (expt p exponent))))

(defun thousand-theorems-q1057919-ispretransitive-of-finite-statement
    (carrier multiplication inverse identity p sylows)
  (implies
   (and
    (q1057919-group-p
     carrier multiplication inverse identity)
    (q1057919-primep p)
    (q1057919-finite-sylow-enumeration-p
     carrier
     multiplication
     inverse
     identity
     p
     sylows))
   (q1057919-all-sylows-conjugate-p
    carrier multiplication inverse sylows)))

(defun thousand-theorems-q1057919-card-dvd-index-statement
    (carrier
     multiplication
     inverse
     identity
     p
     sylows
     sylow-subgroup
     index)
  (implies
   (and
    (q1057919-group-p
     carrier multiplication inverse identity)
    (q1057919-primep p)
    (q1057919-finite-sylow-enumeration-p
     carrier
     multiplication
     inverse
     identity
     p
     sylows)
    (q1057919-sylow-p
     carrier
     multiplication
     inverse
     identity
     p
     sylow-subgroup)
    (q1057919-subgroup-index-p
     carrier
     sylow-subgroup
     multiplication
     inverse
     index))
   (q1057919-divides-p (len sylows) index)))

(defun thousand-theorems-q1057919-card-sylow-modeq-one-statement
    (carrier multiplication inverse identity p sylows)
  (implies
   (and
    (q1057919-group-p
     carrier multiplication inverse identity)
    (q1057919-primep p)
    (q1057919-finite-sylow-enumeration-p
     carrier
     multiplication
     inverse
     identity
     p
     sylows))
   (equal (mod (len sylows) p)
          (mod 1 p))))

(value-triple :itpeval-statement-checked)
:q
