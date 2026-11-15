;; Statement-only formalization of the Babel-formal artifact
;; integral_comp_neg_Iic. The arbitrary source carrier, functions, and
;; predicates remain arbitrary here; no finite enumeration is used.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The token R-TYPE identifies an arbitrary carrier together with its RField
;; operations. INTEGRAL-TYPE distinguishes integral structures on that carrier.

(defstub icni-member-p (r-type x) t)

(defstub icni-zero (r-type) t)
(defstub icni-one (r-type) t)
(defstub icni-add (r-type x y) t)
(defstub icni-opp (r-type x) t)
(defstub icni-mul (r-type x y) t)
(defstub icni-le (r-type x y) t)
(defstub icni-lt (r-type x y) t)
(defstub icni-abs (r-type x) t)

;; ACL2 is first order, so arbitrary source functions and predicates are
;; represented by codes interpreted by these two conservative evaluators.
;; Tagged codes below represent the lambda terms constructed in the source.

(defstub icni-base-function-value (r-type function-code x) t)
(defstub icni-base-domain-holds (r-type domain-code x) t)

(defun icni-function-const (value)
  (list :icni-const value))

(defun icni-function-opp (function)
  (list :icni-opp function))

(defun icni-function-add (function-f function-g)
  (list :icni-add function-f function-g))

(defun icni-function-scale (coefficient function)
  (list :icni-scale coefficient function))

(defun icni-function-abs (function)
  (list :icni-abs function))

(defun icni-function-compose (outer-function inner-function)
  (list :icni-compose outer-function inner-function))

(defun icni-function-carrier-opp ()
  (list :icni-carrier-opp))

(defun icni-function-value (r-type function x)
  (cond
   ((and (consp function)
         (eq (car function) :icni-const))
    (cadr function))
   ((and (consp function)
         (eq (car function) :icni-opp))
    (icni-opp
     r-type
     (icni-function-value r-type (cadr function) x)))
   ((and (consp function)
         (eq (car function) :icni-add))
    (icni-add
     r-type
     (icni-function-value r-type (cadr function) x)
     (icni-function-value r-type (caddr function) x)))
   ((and (consp function)
         (eq (car function) :icni-scale))
    (icni-mul
     r-type
     (cadr function)
     (icni-function-value r-type (caddr function) x)))
   ((and (consp function)
         (eq (car function) :icni-abs))
    (icni-abs
     r-type
     (icni-function-value r-type (cadr function) x)))
   ((and (consp function)
         (eq (car function) :icni-compose))
    (icni-function-value
     r-type
     (cadr function)
     (icni-function-value r-type (caddr function) x)))
   ((and (consp function)
         (eq (car function) :icni-carrier-opp))
    (icni-opp r-type x))
   (t
    (icni-base-function-value r-type function x))))

(defun icni-domain-false ()
  (list :icni-false))

(defun icni-domain-iic (cutoff)
  (list :icni-iic cutoff))

(defun icni-domain-ioi (cutoff)
  (list :icni-ioi cutoff))

(defun icni-domain-iio (cutoff)
  (list :icni-iio cutoff))

(defun icni-domain-union (domain-d domain-e)
  (list :icni-union domain-d domain-e))

(defun icni-domain-inter (domain-d domain-e)
  (list :icni-inter domain-d domain-e))

(defun icni-domain-difference (domain-d domain-p)
  (list :icni-difference domain-d domain-p))

(defun icni-domain-preimage (function domain)
  (list :icni-preimage function domain))

(defun icni-domain-holds (r-type domain x)
  (cond
   ((and (consp domain)
         (eq (car domain) :icni-false))
    nil)
   ((and (consp domain)
         (eq (car domain) :icni-iic))
    (icni-le r-type x (cadr domain)))
   ((and (consp domain)
         (eq (car domain) :icni-ioi))
    (icni-lt r-type (cadr domain) x))
   ((and (consp domain)
         (eq (car domain) :icni-iio))
    (icni-lt r-type x (cadr domain)))
   ((and (consp domain)
         (eq (car domain) :icni-union))
    (or
     (icni-domain-holds r-type (cadr domain) x)
     (icni-domain-holds r-type (caddr domain) x)))
   ((and (consp domain)
         (eq (car domain) :icni-inter))
    (and
     (icni-domain-holds r-type (cadr domain) x)
     (icni-domain-holds r-type (caddr domain) x)))
   ((and (consp domain)
         (eq (car domain) :icni-difference))
    (and
     (icni-domain-holds r-type (cadr domain) x)
     (not
      (icni-domain-holds r-type (caddr domain) x))))
   ((and (consp domain)
         (eq (car domain) :icni-preimage))
    (icni-domain-holds
     r-type
     (caddr domain)
     (icni-function-value r-type (cadr domain) x)))
   (t
    (icni-base-domain-holds r-type domain x))))

(defstub icni-sigma (r-type integral-type domain function) t)

(defun-sk icni-function-typed-p (r-type function)
  (forall (x)
    (implies
     (icni-member-p r-type x)
     (icni-member-p
      r-type
      (icni-function-value r-type function x)))))

(defun-sk icni-functions-agree-on-p
    (r-type domain function-f function-g)
  (forall (x)
    (implies
     (and
      (icni-member-p r-type x)
      (icni-domain-holds r-type domain x))
     (equal
      (icni-function-value r-type function-f x)
      (icni-function-value r-type function-g x)))))

(defun-sk icni-functions-ordered-on-p
    (r-type domain function-f function-g)
  (forall (x)
    (implies
     (and
      (icni-member-p r-type x)
      (icni-domain-holds r-type domain x))
     (icni-le
      r-type
      (icni-function-value r-type function-f x)
      (icni-function-value r-type function-g x)))))

(defun-sk icni-function-nonnegative-on-p
    (r-type domain function)
  (forall (x)
    (implies
     (and
      (icni-member-p r-type x)
      (icni-domain-holds r-type domain x))
     (icni-le
      r-type
      (icni-zero r-type)
      (icni-function-value r-type function x)))))

(defun-sk icni-domains-disjoint-p
    (r-type domain-d domain-e)
  (forall (x)
    (implies
     (icni-member-p r-type x)
     (not
      (and
       (icni-domain-holds r-type domain-d x)
       (icni-domain-holds r-type domain-e x))))))

(defun-sk icni-domains-equal-p
    (r-type domain-d domain-e)
  (forall (x)
    (implies
     (icni-member-p r-type x)
     (iff
      (icni-domain-holds r-type domain-d x)
      (icni-domain-holds r-type domain-e x)))))

(defun-sk icni-domain-decidable-on-p
    (r-type domain-d domain-p)
  (forall (x)
    (implies
     (and
      (icni-member-p r-type x)
      (icni-domain-holds r-type domain-d x))
     (or
      (icni-domain-holds r-type domain-p x)
      (not
       (icni-domain-holds r-type domain-p x))))))

;; The source RField class has exactly these 26 laws. Splitting laws by
;; arity keeps ACL2 admission tractable without changing their conjunction.

(defun-sk icni-rfield-unary-laws-p (r-type)
  (forall (x)
    (implies
     (icni-member-p r-type x)
     (let ((zero (icni-zero r-type))
           (one (icni-one r-type)))
       (and
        (icni-member-p r-type (icni-opp r-type x))
        (icni-member-p r-type (icni-abs r-type x))
        (equal (icni-add r-type x zero) x)
        (equal
         (icni-add r-type (icni-opp r-type x) x)
         zero)
        (equal (icni-mul r-type x one) x)
        (equal
         (icni-opp r-type (icni-opp r-type x))
         x)
        (icni-le r-type x x)
        (implies
         (icni-le r-type zero x)
         (equal (icni-abs r-type x) x))
        (implies
         (icni-le r-type x zero)
         (equal
          (icni-abs r-type x)
          (icni-opp r-type x)))
        (icni-le
         r-type zero (icni-abs r-type x))
        (equal
         (icni-abs r-type (icni-opp r-type x))
         (icni-abs r-type x)))))))

(defun-sk icni-rfield-binary-laws-p (r-type)
  (forall (x y)
    (implies
     (and
      (icni-member-p r-type x)
      (icni-member-p r-type y))
     (and
      (icni-member-p r-type (icni-add r-type x y))
      (icni-member-p r-type (icni-mul r-type x y))
      (equal
       (icni-add r-type x y)
       (icni-add r-type y x))
      (equal
       (icni-mul r-type x y)
       (icni-mul r-type y x))
      (or
       (icni-le r-type x y)
       (icni-le r-type y x))
      (or
       (icni-le r-type x y)
       (not (icni-le r-type x y)))
      (implies
       (icni-le r-type x y)
       (icni-le
        r-type
        (icni-opp r-type y)
        (icni-opp r-type x)))
      (implies
       (and
        (icni-le r-type x y)
        (icni-le r-type y x))
       (equal x y))
      (implies
       (icni-lt r-type x y)
       (icni-lt
        r-type
        (icni-opp r-type y)
        (icni-opp r-type x)))
      (iff
       (icni-lt r-type x y)
       (and
        (icni-le r-type x y)
        (not (equal x y))))
      (icni-le
       r-type
       (icni-abs r-type (icni-add r-type x y))
       (icni-add
        r-type
        (icni-abs r-type x)
        (icni-abs r-type y)))))))

(defun-sk icni-rfield-ternary-laws-p (r-type)
  (forall (x y z)
    (implies
     (and
      (icni-member-p r-type x)
      (icni-member-p r-type y)
      (icni-member-p r-type z))
     (let ((zero (icni-zero r-type)))
       (and
        (equal
         (icni-add r-type (icni-add r-type x y) z)
         (icni-add r-type x (icni-add r-type y z)))
        (implies
         (equal
          (icni-add r-type x z)
          (icni-add r-type y z))
         (equal x y))
        (equal
         (icni-mul r-type (icni-mul r-type x y) z)
         (icni-mul r-type x (icni-mul r-type y z)))
        (equal
         (icni-mul r-type x (icni-add r-type y z))
         (icni-add
          r-type
          (icni-mul r-type x y)
          (icni-mul r-type x z)))
        (implies
         (icni-le r-type x y)
         (icni-le
          r-type
          (icni-add r-type x z)
          (icni-add r-type y z)))
        (implies
         (and
          (icni-le r-type zero z)
          (icni-le r-type x y))
         (icni-le
          r-type
          (icni-mul r-type x z)
          (icni-mul r-type y z)))
        (implies
         (and
          (icni-le r-type x y)
          (icni-le r-type y z))
         (icni-le r-type x z)))))))

(defun icni-rfield-laws-p (r-type)
  (and
   (icni-rfield-unary-laws-p r-type)
   (icni-rfield-binary-laws-p r-type)
   (icni-rfield-ternary-laws-p r-type)))

(defun icni-rfield-p (r-type)
  (and
   (icni-member-p r-type (icni-zero r-type))
   (icni-member-p r-type (icni-one r-type))
   (icni-le r-type (icni-zero r-type) (icni-one r-type))
   (icni-rfield-laws-p r-type)))

;; The source Integral class has exactly seven laws. The closure predicate
;; expresses SIGMA's source result type and is not an additional algebraic law.

(defun-sk icni-sigma-closed-p (r-type integral-type)
  (forall (domain function)
    (implies
     (icni-function-typed-p r-type function)
     (icni-member-p
      r-type
      (icni-sigma
       r-type integral-type domain function)))))

(defun-sk icni-sigma-mul-const-law-p (r-type integral-type)
  (forall (domain function coefficient)
    (implies
     (and
      (icni-function-typed-p r-type function)
      (icni-member-p r-type coefficient))
     (equal
      (icni-sigma
       r-type
       integral-type
       domain
       (icni-function-scale coefficient function))
      (icni-mul
       r-type
       coefficient
       (icni-sigma
        r-type integral-type domain function))))))

(defun-sk icni-sigma-congr-law-p (r-type integral-type)
  (forall (domain function-f function-g)
    (implies
     (and
      (icni-function-typed-p r-type function-f)
      (icni-function-typed-p r-type function-g)
      (icni-functions-agree-on-p
       r-type domain function-f function-g))
     (equal
      (icni-sigma
       r-type integral-type domain function-f)
      (icni-sigma
       r-type integral-type domain function-g)))))

(defun-sk icni-sigma-zero-law-p (r-type integral-type)
  (forall (domain)
    (equal
     (icni-sigma
      r-type
      integral-type
      domain
      (icni-function-const (icni-zero r-type)))
     (icni-zero r-type))))

(defun-sk icni-sigma-add-law-p (r-type integral-type)
  (forall (domain function-f function-g)
    (implies
     (and
      (icni-function-typed-p r-type function-f)
      (icni-function-typed-p r-type function-g))
     (equal
      (icni-sigma
       r-type
       integral-type
       domain
       (icni-function-add function-f function-g))
      (icni-add
       r-type
       (icni-sigma
        r-type integral-type domain function-f)
       (icni-sigma
        r-type integral-type domain function-g))))))

(defun-sk icni-sigma-union-law-p (r-type integral-type)
  (forall (domain-d domain-e function)
    (implies
     (and
      (icni-function-typed-p r-type function)
      (icni-domains-disjoint-p
       r-type domain-d domain-e))
     (equal
      (icni-sigma
       r-type
       integral-type
       (icni-domain-union domain-d domain-e)
       function)
      (icni-add
       r-type
       (icni-sigma
        r-type integral-type domain-d function)
       (icni-sigma
        r-type integral-type domain-e function))))))

(defun-sk icni-sigma-le-law-p (r-type integral-type)
  (forall (domain function-f function-g)
    (implies
     (and
      (icni-function-typed-p r-type function-f)
      (icni-function-typed-p r-type function-g)
      (icni-functions-ordered-on-p
       r-type domain function-f function-g))
     (icni-le
      r-type
      (icni-sigma
       r-type integral-type domain function-f)
      (icni-sigma
       r-type integral-type domain function-g)))))

(defun-sk icni-sigma-domain-congr-law-p (r-type integral-type)
  (forall (domain-d domain-e function)
    (implies
     (and
      (icni-function-typed-p r-type function)
      (icni-domains-equal-p
       r-type domain-d domain-e))
     (equal
      (icni-sigma
       r-type integral-type domain-d function)
      (icni-sigma
       r-type integral-type domain-e function)))))

(defun icni-integral-laws-p (r-type integral-type)
  (and
   (icni-sigma-closed-p r-type integral-type)
   (icni-sigma-mul-const-law-p r-type integral-type)
   (icni-sigma-congr-law-p r-type integral-type)
   (icni-sigma-zero-law-p r-type integral-type)
   (icni-sigma-add-law-p r-type integral-type)
   (icni-sigma-union-law-p r-type integral-type)
   (icni-sigma-le-law-p r-type integral-type)
   (icni-sigma-domain-congr-law-p r-type integral-type)))

(defun icni-integral-context-p (r-type integral-type)
  (and
   (icni-rfield-p r-type)
   (icni-integral-laws-p r-type integral-type)))

;; Each predicate below corresponds, in source order, to one indexed theorem.

(defun-sk icni-lt-irrefl-statement ()
  (forall (r-type integral-type x)
    (implies
     (and
      (icni-integral-context-p r-type integral-type)
      (icni-member-p r-type x))
     (not (icni-lt r-type x x)))))

(defun-sk icni-lt-trans-strict-statement ()
  (forall (r-type integral-type x y z)
    (implies
     (and
      (icni-integral-context-p r-type integral-type)
      (icni-member-p r-type x)
      (icni-member-p r-type y)
      (icni-member-p r-type z)
      (icni-lt r-type x y)
      (icni-lt r-type y z))
     (icni-lt r-type x z))))

(defun-sk icni-preimage-union-statement ()
  (forall (r-type domain-d domain-e function-g x)
    (implies
     (and
      (icni-function-typed-p r-type function-g)
      (icni-member-p r-type x))
     (iff
      (icni-domain-holds
       r-type
       (icni-domain-preimage
        function-g
        (icni-domain-union domain-d domain-e))
       x)
      (or
       (icni-domain-holds
        r-type
        (icni-domain-preimage function-g domain-d)
        x)
       (icni-domain-holds
        r-type
        (icni-domain-preimage function-g domain-e)
        x))))))

(defun-sk icni-preimage-inter-statement ()
  (forall (r-type domain-d domain-e function-g x)
    (implies
     (and
      (icni-function-typed-p r-type function-g)
      (icni-member-p r-type x))
     (iff
      (icni-domain-holds
       r-type
       (icni-domain-preimage
        function-g
        (icni-domain-inter domain-d domain-e))
       x)
      (and
       (icni-domain-holds
        r-type
        (icni-domain-preimage function-g domain-d)
        x)
       (icni-domain-holds
        r-type
        (icni-domain-preimage function-g domain-e)
        x))))))

(defun-sk icni-preimage-neg-ioi-statement ()
  (forall (r-type integral-type cutoff x)
    (implies
     (and
      (icni-integral-context-p r-type integral-type)
      (icni-member-p r-type cutoff)
      (icni-member-p r-type x))
     (iff
      (icni-domain-holds
       r-type
       (icni-domain-preimage
        (icni-function-carrier-opp)
        (icni-domain-ioi cutoff))
       x)
      (icni-lt r-type x (icni-opp r-type cutoff))))))

(defun-sk icni-preimage-neg-iic-statement ()
  (forall (r-type integral-type cutoff x)
    (implies
     (and
      (icni-integral-context-p r-type integral-type)
      (icni-member-p r-type cutoff)
      (icni-member-p r-type x))
     (iff
      (icni-domain-holds
       r-type
       (icni-domain-preimage
        (icni-function-carrier-opp)
        (icni-domain-iic cutoff))
       x)
      (icni-le r-type (icni-opp r-type cutoff) x)))))

(defun-sk icni-preimage-comp-statement ()
  (forall
   (r-type domain-d function-g function-h x)
    (implies
     (and
      (icni-function-typed-p r-type function-g)
      (icni-function-typed-p r-type function-h)
      (icni-member-p r-type x))
     (iff
      (icni-domain-holds
       r-type
       (icni-domain-preimage
        function-g
        (icni-domain-preimage function-h domain-d))
       x)
      (icni-domain-holds
       r-type
       (icni-domain-preimage
        (icni-function-compose function-h function-g)
        domain-d)
       x)))))

(defun-sk icni-integral-neg-statement ()
  (forall (r-type integral-type domain-d function-f)
    (implies
     (and
      (icni-integral-context-p r-type integral-type)
      (icni-function-typed-p r-type function-f))
     (equal
      (icni-sigma
       r-type
       integral-type
       domain-d
       (icni-function-opp function-f))
      (icni-opp
       r-type
       (icni-sigma
        r-type integral-type domain-d function-f))))))

(defun-sk icni-integral-sub-statement ()
  (forall (r-type integral-type domain-d function-f function-g)
    (implies
     (and
      (icni-integral-context-p r-type integral-type)
      (icni-function-typed-p r-type function-f)
      (icni-function-typed-p r-type function-g))
     (equal
      (icni-sigma
       r-type
       integral-type
       domain-d
       (icni-function-add
        function-f
        (icni-function-opp function-g)))
      (icni-add
       r-type
       (icni-sigma
        r-type integral-type domain-d function-f)
       (icni-opp
        r-type
        (icni-sigma
         r-type integral-type domain-d function-g)))))))

(defun-sk icni-sigma-empty-statement ()
  (forall (r-type integral-type function-f)
    (implies
     (and
      (icni-integral-context-p r-type integral-type)
      (icni-function-typed-p r-type function-f))
     (equal
      (icni-sigma
       r-type
       integral-type
       (icni-domain-false)
       function-f)
      (icni-zero r-type)))))

(defun-sk icni-sigma-bilinear-statement ()
  (forall
   (r-type integral-type domain-d function-f function-g
           coefficient-c coefficient-d)
    (implies
     (and
      (icni-integral-context-p r-type integral-type)
      (icni-function-typed-p r-type function-f)
      (icni-function-typed-p r-type function-g)
      (icni-member-p r-type coefficient-c)
      (icni-member-p r-type coefficient-d))
     (equal
      (icni-sigma
       r-type
       integral-type
       domain-d
       (icni-function-add
        (icni-function-scale coefficient-c function-f)
        (icni-function-scale coefficient-d function-g)))
      (icni-add
       r-type
       (icni-mul
        r-type
        coefficient-c
        (icni-sigma
         r-type integral-type domain-d function-f))
       (icni-mul
        r-type
        coefficient-d
        (icni-sigma
         r-type integral-type domain-d function-g)))))))

(defun-sk icni-sigma-le-monotone-statement ()
  (forall (r-type integral-type domain-d function-f function-g)
    (implies
     (and
      (icni-integral-context-p r-type integral-type)
      (icni-function-typed-p r-type function-f)
      (icni-function-typed-p r-type function-g)
      (icni-functions-ordered-on-p
       r-type domain-d function-f function-g))
     (icni-le
      r-type
      (icni-sigma
       r-type integral-type domain-d function-f)
      (icni-sigma
       r-type integral-type domain-d function-g)))))

(defun-sk icni-sigma-nonneg-statement ()
  (forall (r-type integral-type domain-d function-f)
    (implies
     (and
      (icni-integral-context-p r-type integral-type)
      (icni-function-typed-p r-type function-f)
      (icni-function-nonnegative-on-p
       r-type domain-d function-f))
     (icni-le
      r-type
      (icni-zero r-type)
      (icni-sigma
       r-type integral-type domain-d function-f)))))

(defun-sk icni-sigma-split-statement ()
  (forall
   (r-type integral-type domain-d domain-p function-f)
    (implies
     (and
      (icni-integral-context-p r-type integral-type)
      (icni-function-typed-p r-type function-f)
      (icni-domain-decidable-on-p
       r-type domain-d domain-p))
     (equal
      (icni-sigma
       r-type integral-type domain-d function-f)
      (icni-add
       r-type
       (icni-sigma
        r-type
        integral-type
        (icni-domain-inter domain-d domain-p)
        function-f)
       (icni-sigma
        r-type
        integral-type
        (icni-domain-difference domain-d domain-p)
        function-f))))))

(defun-sk icni-sigma-preimage-neg-ioi-statement ()
  (forall (r-type integral-type function-f cutoff)
    (implies
     (and
      (icni-integral-context-p r-type integral-type)
      (icni-function-typed-p r-type function-f)
      (icni-member-p r-type cutoff))
     (equal
      (icni-sigma
       r-type
       integral-type
       (icni-domain-preimage
        (icni-function-carrier-opp)
        (icni-domain-ioi cutoff))
       function-f)
      (icni-sigma
       r-type
       integral-type
       (icni-domain-iio (icni-opp r-type cutoff))
       function-f)))))

(defun-sk icni-sigma-abs-bound-statement ()
  (forall (r-type integral-type domain-d function-f)
    (implies
     (and
      (icni-integral-context-p r-type integral-type)
      (icni-function-typed-p r-type function-f))
     (icni-le
      r-type
      (icni-abs
       r-type
       (icni-sigma
        r-type integral-type domain-d function-f))
      (icni-sigma
       r-type
       integral-type
       domain-d
       (icni-function-abs function-f))))))

(defun integral-comp-neg-iic-statement ()
  (and
   (icni-lt-irrefl-statement)
   (icni-lt-trans-strict-statement)
   (icni-preimage-union-statement)
   (icni-preimage-inter-statement)
   (icni-preimage-neg-ioi-statement)
   (icni-preimage-neg-iic-statement)
   (icni-preimage-comp-statement)
   (icni-integral-neg-statement)
   (icni-integral-sub-statement)
   (icni-sigma-empty-statement)
   (icni-sigma-bilinear-statement)
   (icni-sigma-le-monotone-statement)
   (icni-sigma-nonneg-statement)
   (icni-sigma-split-statement)
   (icni-sigma-preimage-neg-ioi-statement)
   (icni-sigma-abs-bound-statement)))

(value-triple :itpeval-statement-checked)
:q
