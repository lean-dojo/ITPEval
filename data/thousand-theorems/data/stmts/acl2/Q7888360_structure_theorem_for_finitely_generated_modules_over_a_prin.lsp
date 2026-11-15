;; Statement-only formalization of thousand-theorems corpus artifact Q7888360,
;; "Structure theorem for finitely generated modules over a principal ideal
;; domain": every finitely generated module over a commutative principal ideal
;; domain is R-linearly equivalent to a finite free module times a finite
;; direct sum of quotients by irreducible prime powers. This file contains no
;; proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Tame function objects represent arbitrary ring and module carriers,
;; operations, and the internally existential linear equivalence. A finite
;; index type is represented by Fin k. Quotient elements are represented by
;; ring elements modulo the corresponding principal-ideal congruence.

(defun q7888360-app1 (function x)
  (apply$ function (list x)))

(defun q7888360-app2 (function x y)
  (apply$ function (list x y)))

(defun q7888360-member-p (carrier value)
  (if (q7888360-app1 carrier value) t nil))

(defun q7888360-ring-add (addition left right)
  (q7888360-app2 addition left right))

(defun q7888360-ring-mul (multiplication left right)
  (q7888360-app2 multiplication left right))

(defun q7888360-ring-neg (negation value)
  (q7888360-app1 negation value))

(defun q7888360-module-add (addition left right)
  (q7888360-app2 addition left right))

(defun q7888360-module-neg (negation value)
  (q7888360-app1 negation value))

(defun q7888360-smul (scalar-action scalar vector)
  (q7888360-app2 scalar-action scalar vector))

;; Commutative rings and integral domains.

(defun-sk q7888360-commutative-ring-laws-p
    (carrier zero one addition multiplication negation)
  (forall (x y z)
    (and
     (implies
      (q7888360-member-p carrier x)
      (and
       (q7888360-member-p
        carrier
        (q7888360-ring-neg negation x))
       (equal (q7888360-ring-add addition x zero) x)
       (equal (q7888360-ring-add addition zero x) x)
       (equal
        (q7888360-ring-add
         addition x (q7888360-ring-neg negation x))
        zero)
       (equal
        (q7888360-ring-add
         addition (q7888360-ring-neg negation x) x)
        zero)
       (equal (q7888360-ring-mul multiplication x one) x)
       (equal (q7888360-ring-mul multiplication one x) x)
       (equal (q7888360-ring-mul multiplication x zero) zero)
       (equal (q7888360-ring-mul multiplication zero x) zero)))
     (implies
      (and
       (q7888360-member-p carrier x)
       (q7888360-member-p carrier y))
      (and
       (q7888360-member-p
        carrier
        (q7888360-ring-add addition x y))
       (q7888360-member-p
        carrier
        (q7888360-ring-mul multiplication x y))
       (equal
        (q7888360-ring-add addition x y)
        (q7888360-ring-add addition y x))
       (equal
        (q7888360-ring-mul multiplication x y)
        (q7888360-ring-mul multiplication y x))))
     (implies
      (and
       (q7888360-member-p carrier x)
       (q7888360-member-p carrier y)
       (q7888360-member-p carrier z))
      (and
       (equal
        (q7888360-ring-add
         addition
         (q7888360-ring-add addition x y)
         z)
        (q7888360-ring-add
         addition
         x
         (q7888360-ring-add addition y z)))
       (equal
        (q7888360-ring-mul
         multiplication
         (q7888360-ring-mul multiplication x y)
         z)
        (q7888360-ring-mul
         multiplication
         x
         (q7888360-ring-mul multiplication y z)))
       (equal
        (q7888360-ring-mul
         multiplication
         x
         (q7888360-ring-add addition y z))
        (q7888360-ring-add
         addition
         (q7888360-ring-mul multiplication x y)
         (q7888360-ring-mul multiplication x z)))
       (equal
        (q7888360-ring-mul
         multiplication
         (q7888360-ring-add addition x y)
         z)
        (q7888360-ring-add
         addition
         (q7888360-ring-mul multiplication x z)
         (q7888360-ring-mul multiplication y z))))))))

(defun q7888360-commutative-ring-p
    (carrier zero one addition multiplication negation)
  (and
   (tamep-functionp carrier)
   (tamep-functionp addition)
   (tamep-functionp multiplication)
   (tamep-functionp negation)
   (q7888360-member-p carrier zero)
   (q7888360-member-p carrier one)
   (q7888360-commutative-ring-laws-p
    carrier zero one addition multiplication negation)))

(defun-sk q7888360-no-zero-divisors-p
    (carrier zero multiplication)
  (forall (x y)
    (implies
     (and
      (q7888360-member-p carrier x)
      (q7888360-member-p carrier y)
      (equal
       (q7888360-ring-mul multiplication x y)
       zero))
     (or (equal x zero)
         (equal y zero)))))

(defun q7888360-domain-p
    (carrier zero one addition multiplication negation)
  (and
   (q7888360-commutative-ring-p
    carrier zero one addition multiplication negation)
   (not (equal zero one))
   (q7888360-no-zero-divisors-p
    carrier zero multiplication)))

;; Ideals and the principal-ideal condition.

(defun-sk q7888360-ideal-laws-p
    (carrier zero addition multiplication negation ideal)
  (forall (a x y)
    (and
     (implies
      (q7888360-member-p ideal x)
      (and
       (q7888360-member-p carrier x)
       (q7888360-member-p
        ideal
        (q7888360-ring-neg negation x))))
     (implies
      (and
       (q7888360-member-p ideal x)
       (q7888360-member-p ideal y))
      (q7888360-member-p
       ideal
       (q7888360-ring-add addition x y)))
     (implies
      (and
       (q7888360-member-p carrier a)
       (q7888360-member-p ideal x))
      (q7888360-member-p
       ideal
       (q7888360-ring-mul multiplication a x))))))

(defun q7888360-ideal-p
    (carrier zero addition multiplication negation ideal)
  (and
   (tamep-functionp ideal)
   (q7888360-member-p ideal zero)
   (q7888360-ideal-laws-p
    carrier zero addition multiplication negation ideal)))

(defun-sk q7888360-principal-member-p
    (carrier multiplication generator value)
  (exists (coefficient)
    (and
     (q7888360-member-p carrier coefficient)
     (equal
      value
      (q7888360-ring-mul
       multiplication coefficient generator)))))

(defun-sk q7888360-ideal-generated-by-p
    (carrier multiplication ideal generator)
  (forall (value)
    (iff
     (q7888360-member-p ideal value)
     (and
      (q7888360-member-p carrier value)
      (q7888360-principal-member-p
       carrier multiplication generator value)))))

(defun-sk q7888360-ideal-generator-exists-p
    (carrier multiplication ideal)
  (exists (generator)
    (and
     (q7888360-member-p carrier generator)
     (q7888360-ideal-generated-by-p
      carrier multiplication ideal generator))))

(defun-sk q7888360-principal-ideal-ring-p
    (carrier zero addition multiplication negation)
  (forall (ideal)
    (implies
     (q7888360-ideal-p
      carrier zero addition multiplication negation ideal)
     (q7888360-ideal-generator-exists-p
      carrier multiplication ideal))))

;; Additive commutative groups and modules.

(defun-sk q7888360-module-laws-p
    (ring-carrier
     ring-zero
     ring-one
     ring-addition
     ring-multiplication
     module-carrier
     module-zero
     module-addition
     module-negation
     scalar-action)
  (forall (a b x y z)
    (and
     (implies
      (q7888360-member-p module-carrier x)
      (and
       (q7888360-member-p
        module-carrier
        (q7888360-module-neg module-negation x))
       (equal
        (q7888360-module-add module-addition x module-zero)
        x)
       (equal
        (q7888360-module-add module-addition module-zero x)
        x)
       (equal
        (q7888360-module-add
         module-addition
         x
         (q7888360-module-neg module-negation x))
        module-zero)
       (equal
        (q7888360-module-add
         module-addition
         (q7888360-module-neg module-negation x)
         x)
        module-zero)
       (equal
        (q7888360-smul scalar-action ring-one x)
        x)
       (equal
        (q7888360-smul scalar-action ring-zero x)
        module-zero)))
     (implies
      (and
       (q7888360-member-p module-carrier x)
       (q7888360-member-p module-carrier y))
      (and
       (q7888360-member-p
        module-carrier
        (q7888360-module-add module-addition x y))
       (equal
        (q7888360-module-add module-addition x y)
        (q7888360-module-add module-addition y x))))
     (implies
      (and
       (q7888360-member-p module-carrier x)
       (q7888360-member-p module-carrier y)
       (q7888360-member-p module-carrier z))
      (equal
       (q7888360-module-add
        module-addition
        (q7888360-module-add module-addition x y)
        z)
       (q7888360-module-add
        module-addition
        x
        (q7888360-module-add module-addition y z))))
     (implies
      (and
       (q7888360-member-p ring-carrier a)
       (q7888360-member-p module-carrier x))
      (and
       (q7888360-member-p
        module-carrier
        (q7888360-smul scalar-action a x))
       (equal
        (q7888360-smul scalar-action a module-zero)
        module-zero)))
     (implies
      (and
       (q7888360-member-p ring-carrier a)
       (q7888360-member-p module-carrier x)
       (q7888360-member-p module-carrier y))
      (equal
       (q7888360-smul
        scalar-action
        a
        (q7888360-module-add module-addition x y))
       (q7888360-module-add
        module-addition
        (q7888360-smul scalar-action a x)
        (q7888360-smul scalar-action a y))))
     (implies
      (and
       (q7888360-member-p ring-carrier a)
       (q7888360-member-p ring-carrier b)
       (q7888360-member-p module-carrier x))
      (and
       (equal
        (q7888360-smul
         scalar-action
         (q7888360-ring-add ring-addition a b)
         x)
        (q7888360-module-add
         module-addition
         (q7888360-smul scalar-action a x)
         (q7888360-smul scalar-action b x)))
       (equal
        (q7888360-smul
         scalar-action
         (q7888360-ring-mul ring-multiplication a b)
         x)
        (q7888360-smul
         scalar-action
         a
         (q7888360-smul scalar-action b x))))))))

(defun q7888360-module-p
    (ring-carrier
     ring-zero
     ring-one
     ring-addition
     ring-multiplication
     module-carrier
     module-zero
     module-addition
     module-negation
     scalar-action)
  (and
   (tamep-functionp module-carrier)
   (tamep-functionp module-addition)
   (tamep-functionp module-negation)
   (tamep-functionp scalar-action)
   (q7888360-member-p module-carrier module-zero)
   (q7888360-module-laws-p
    ring-carrier
    ring-zero
    ring-one
    ring-addition
    ring-multiplication
    module-carrier
    module-zero
    module-addition
    module-negation
    scalar-action)))

;; Finite generation, with coefficient witnesses kept internal.

(defun q7888360-ring-list-p (carrier values)
  (if (consp values)
      (and
       (q7888360-member-p carrier (car values))
       (q7888360-ring-list-p carrier (cdr values)))
    (equal values nil)))

(defun q7888360-module-list-p (carrier values)
  (if (consp values)
      (and
       (q7888360-member-p carrier (car values))
       (q7888360-module-list-p carrier (cdr values)))
    (equal values nil)))

(defun q7888360-linear-combination
    (module-zero module-addition scalar-action generators coefficients)
  (if (and (consp generators) (consp coefficients))
      (q7888360-module-add
       module-addition
       (q7888360-smul
        scalar-action
        (car coefficients)
        (car generators))
       (q7888360-linear-combination
        module-zero
        module-addition
        scalar-action
        (cdr generators)
        (cdr coefficients)))
    module-zero))

(defun-sk q7888360-spanning-coefficients-exist-p
    (ring-carrier
     module-zero
     module-addition
     scalar-action
     generators
     value)
  (exists (coefficients)
    (and
     (true-listp coefficients)
     (equal (len coefficients) (len generators))
     (q7888360-ring-list-p ring-carrier coefficients)
     (equal
      (q7888360-linear-combination
       module-zero
       module-addition
       scalar-action
       generators
       coefficients)
      value))))

(defun-sk q7888360-generators-span-p
    (ring-carrier
     module-carrier
     module-zero
     module-addition
     scalar-action
     generators)
  (forall (value)
    (implies
     (q7888360-member-p module-carrier value)
     (q7888360-spanning-coefficients-exist-p
      ring-carrier
      module-zero
      module-addition
      scalar-action
      generators
      value))))

(defun q7888360-generating-family-p
    (ring-carrier
     module-carrier
     module-zero
     module-addition
     scalar-action
     generators)
  (and
   (true-listp generators)
   (q7888360-module-list-p module-carrier generators)
   (q7888360-generators-span-p
    ring-carrier
    module-carrier
    module-zero
    module-addition
    scalar-action
    generators)))

(defun-sk q7888360-finitely-generated-p
    (ring-carrier
     module-carrier
     module-zero
     module-addition
     scalar-action)
  (exists (generators)
    (q7888360-generating-family-p
     ring-carrier
     module-carrier
     module-zero
     module-addition
     scalar-action
     generators)))

;; Irreducibles and prime powers.

(defun-sk q7888360-unit-p
    (carrier one multiplication value)
  (exists (inverse)
    (and
     (q7888360-member-p carrier inverse)
     (equal
      (q7888360-ring-mul multiplication value inverse)
      one))))

(defun-sk q7888360-irreducible-factor-law-p
    (carrier one multiplication value)
  (forall (left right)
    (implies
     (and
      (q7888360-member-p carrier left)
      (q7888360-member-p carrier right)
      (equal
       (q7888360-ring-mul multiplication left right)
       value))
     (or
      (q7888360-unit-p
       carrier one multiplication left)
      (q7888360-unit-p
       carrier one multiplication right)))))

(defun q7888360-irreducible-p
    (carrier zero one multiplication value)
  (and
   (q7888360-member-p carrier value)
   (not (equal value zero))
   (not
    (q7888360-unit-p
     carrier one multiplication value))
   (q7888360-irreducible-factor-law-p
    carrier one multiplication value)))

(defun q7888360-all-irreducible-p
    (carrier zero one multiplication values)
  (if (consp values)
      (and
       (q7888360-irreducible-p
        carrier zero one multiplication (car values))
       (q7888360-all-irreducible-p
        carrier zero one multiplication (cdr values)))
    (equal values nil)))

(defun q7888360-natural-list-p (values)
  (if (consp values)
      (and
       (natp (car values))
       (q7888360-natural-list-p (cdr values)))
    (equal values nil)))

(defun q7888360-ring-power
    (one multiplication base exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      one
    (q7888360-ring-mul
     multiplication
     base
     (q7888360-ring-power
      one multiplication base (1- exponent)))))

;; The target is R^n times the finite direct sum of R/(p_i^e_i). The second
;; factor uses representative lists and an explicit quotient congruence.

(defun q7888360-fixed-ring-list-p (carrier size values)
  (and
   (true-listp values)
   (equal (len values) size)
   (q7888360-ring-list-p carrier values)))

(defun q7888360-codomain-representative-p
    (ring-carrier free-rank torsion-size value)
  (and
   (true-listp value)
   (equal (len value) 2)
   (q7888360-fixed-ring-list-p
    ring-carrier free-rank (car value))
   (q7888360-fixed-ring-list-p
    ring-carrier torsion-size (cadr value))))

(defun-sk q7888360-principal-congruent-p
    (carrier addition multiplication negation modulus left right)
  (exists (coefficient)
    (and
     (q7888360-member-p carrier coefficient)
     (equal
      (q7888360-ring-add
       addition left (q7888360-ring-neg negation right))
      (q7888360-ring-mul
       multiplication coefficient modulus)))))

(defun q7888360-quotient-lists-equivalent-p
    (carrier one addition multiplication negation
     primes exponents left right)
  (if (consp primes)
      (and
       (consp exponents)
       (consp left)
       (consp right)
       (q7888360-principal-congruent-p
        carrier
        addition
        multiplication
        negation
        (q7888360-ring-power
         one multiplication (car primes) (car exponents))
        (car left)
        (car right))
       (q7888360-quotient-lists-equivalent-p
        carrier
        one
        addition
        multiplication
        negation
        (cdr primes)
        (cdr exponents)
        (cdr left)
        (cdr right)))
    (and
     (equal exponents nil)
     (equal left nil)
     (equal right nil))))

(defun q7888360-codomain-equivalent-p
    (carrier one addition multiplication negation
     primes exponents left right)
  (and
   (equal (car left) (car right))
   (q7888360-quotient-lists-equivalent-p
    carrier
    one
    addition
    multiplication
    negation
    primes
    exponents
    (cadr left)
    (cadr right))))

(defun q7888360-ring-list-add (addition left right)
  (if (and (consp left) (consp right))
      (cons
       (q7888360-ring-add addition (car left) (car right))
       (q7888360-ring-list-add
        addition (cdr left) (cdr right)))
    nil))

(defun q7888360-ring-list-smul (multiplication scalar values)
  (if (consp values)
      (cons
       (q7888360-ring-mul multiplication scalar (car values))
       (q7888360-ring-list-smul
        multiplication scalar (cdr values)))
    nil))

(defun q7888360-codomain-add (addition left right)
  (list
   (q7888360-ring-list-add
    addition (car left) (car right))
   (q7888360-ring-list-add
    addition (cadr left) (cadr right))))

(defun q7888360-codomain-smul (multiplication scalar value)
  (list
   (q7888360-ring-list-smul
    multiplication scalar (car value))
   (q7888360-ring-list-smul
    multiplication scalar (cadr value))))

(defun-sk q7888360-codomain-preimage-exists-p
    (ring-carrier
     ring-one
     ring-addition
     ring-multiplication
     ring-negation
     module-carrier
     primes
     exponents
     forward
     target)
  (exists (source)
    (and
     (q7888360-member-p module-carrier source)
     (q7888360-codomain-equivalent-p
      ring-carrier
      ring-one
      ring-addition
      ring-multiplication
      ring-negation
      primes
      exponents
      (q7888360-app1 forward source)
      target))))

(defun-sk q7888360-linear-equivalence-laws-p
    (ring-carrier
     ring-one
     ring-addition
     ring-multiplication
     ring-negation
     module-carrier
     module-addition
     scalar-action
     free-rank
     torsion-size
     primes
     exponents
     forward)
  (forall (x y scalar target)
    (and
     (implies
      (q7888360-member-p module-carrier x)
      (q7888360-codomain-representative-p
       ring-carrier
       free-rank
       torsion-size
       (q7888360-app1 forward x)))
     (implies
      (q7888360-codomain-representative-p
       ring-carrier free-rank torsion-size target)
      (q7888360-codomain-preimage-exists-p
       ring-carrier
       ring-one
       ring-addition
       ring-multiplication
       ring-negation
       module-carrier
       primes
       exponents
       forward
       target))
     (implies
      (and
       (q7888360-member-p module-carrier x)
       (q7888360-member-p module-carrier y))
      (and
       (q7888360-codomain-equivalent-p
        ring-carrier
        ring-one
        ring-addition
        ring-multiplication
        ring-negation
        primes
        exponents
        (q7888360-app1
         forward
         (q7888360-module-add module-addition x y))
        (q7888360-codomain-add
         ring-addition
         (q7888360-app1 forward x)
         (q7888360-app1 forward y)))
       (iff
        (equal x y)
        (q7888360-codomain-equivalent-p
         ring-carrier
         ring-one
         ring-addition
         ring-multiplication
         ring-negation
         primes
         exponents
         (q7888360-app1 forward x)
         (q7888360-app1 forward y)))))
     (implies
      (and
       (q7888360-member-p ring-carrier scalar)
       (q7888360-member-p module-carrier x))
      (q7888360-codomain-equivalent-p
       ring-carrier
       ring-one
       ring-addition
       ring-multiplication
       ring-negation
       primes
       exponents
       (q7888360-app1
        forward
        (q7888360-smul scalar-action scalar x))
       (q7888360-codomain-smul
        ring-multiplication
        scalar
        (q7888360-app1 forward x)))))))

(defun q7888360-linear-equivalence-p
    (ring-carrier
     ring-one
     ring-addition
     ring-multiplication
     ring-negation
     module-carrier
     module-addition
     scalar-action
     free-rank
     torsion-size
     primes
     exponents
     forward)
  (and
   (tamep-functionp forward)
   (q7888360-linear-equivalence-laws-p
    ring-carrier
    ring-one
    ring-addition
    ring-multiplication
    ring-negation
    module-carrier
    module-addition
    scalar-action
    free-rank
    torsion-size
    primes
    exponents
    forward)))

(defun q7888360-decomposition-witness-p
    (ring-carrier
     ring-zero
     ring-one
     ring-addition
     ring-multiplication
     ring-negation
     module-carrier
     module-addition
     scalar-action
     free-rank
     torsion-size
     primes
     exponents
     forward)
  (and
   (natp free-rank)
   (natp torsion-size)
   (true-listp primes)
   (equal (len primes) torsion-size)
   (q7888360-ring-list-p ring-carrier primes)
   (q7888360-all-irreducible-p
    ring-carrier
    ring-zero
    ring-one
    ring-multiplication
    primes)
   (true-listp exponents)
   (equal (len exponents) torsion-size)
   (q7888360-natural-list-p exponents)
   (q7888360-linear-equivalence-p
    ring-carrier
    ring-one
    ring-addition
    ring-multiplication
    ring-negation
    module-carrier
    module-addition
    scalar-action
    free-rank
    torsion-size
    primes
    exponents
    forward)))

(defun-sk q7888360-decomposition-exists-p
    (ring-carrier
     ring-zero
     ring-one
     ring-addition
     ring-multiplication
     ring-negation
     module-carrier
     module-addition
     scalar-action)
  (exists
   (free-rank torsion-size primes exponents forward)
   (q7888360-decomposition-witness-p
    ring-carrier
    ring-zero
    ring-one
    ring-addition
    ring-multiplication
    ring-negation
    module-carrier
    module-addition
    scalar-action
    free-rank
    torsion-size
    primes
    exponents
    forward)))

(defun-sk
    thousand-theorems-q7888360-structure-theorem-for-finitely-generated-modules-over-a-pid-statement
    ()
  (forall
   (ring-carrier
    ring-zero
    ring-one
    ring-addition
    ring-multiplication
    ring-negation
    module-carrier
    module-zero
    module-addition
    module-negation
    scalar-action)
   (implies
    (and
     (q7888360-domain-p
      ring-carrier
      ring-zero
      ring-one
      ring-addition
      ring-multiplication
      ring-negation)
     (q7888360-principal-ideal-ring-p
      ring-carrier
      ring-zero
      ring-addition
      ring-multiplication
      ring-negation)
     (q7888360-module-p
      ring-carrier
      ring-zero
      ring-one
      ring-addition
      ring-multiplication
      module-carrier
      module-zero
      module-addition
      module-negation
      scalar-action)
     (q7888360-finitely-generated-p
      ring-carrier
      module-carrier
      module-zero
      module-addition
      scalar-action))
    (q7888360-decomposition-exists-p
     ring-carrier
     ring-zero
     ring-one
     ring-addition
     ring-multiplication
     ring-negation
     module-carrier
     module-addition
     scalar-action))))

(value-triple :itpeval-statement-checked)
:q
