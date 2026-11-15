;; Statement-only formalization of thousand-theorems corpus artifact Q245098,
;; "Intermediate value theorem": a function continuous on a closed interval
;; in a dense conditionally complete linear order attains every ordered value
;; between its endpoint values. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Tame APPLY$ predicates and functions present arbitrary carriers, sets,
;; relations, and maps. FN-EQUAL supplies unbounded universal quantification;
;; inequality with a constant-false function supplies internal existential
;; quantification. The domain topology is definitionally eliminated in favor
;; of the interval basis for its OrderTopology. The codomain topology is
;; presented by its neighborhood relation, with the standard neighborhood
;; axioms and the separation condition equivalent to closedness of <=.

(defun q245098-quoted (object)
  (list 'quote object))

(defun q245098-term-list (terms)
  (if (consp terms)
      (list 'cons
            (car terms)
            (q245098-term-list (cdr terms)))
    (q245098-quoted nil)))

(defun q245098-apply-term (function-term arguments)
  (list 'apply$
        function-term
        (q245098-term-list arguments)))

(defun q245098-static-apply-term (function arguments)
  (q245098-apply-term
   (q245098-quoted function)
   arguments))

(defun q245098-and-terms (terms)
  (if (consp terms)
      (list 'if
            (car terms)
            (q245098-and-terms (cdr terms))
            (q245098-quoted nil))
    (q245098-quoted t)))

(defun q245098-not-term (term)
  (list 'if term
        (q245098-quoted nil)
        (q245098-quoted t)))

(defun q245098-implies-term (hypothesis conclusion)
  (list 'if hypothesis conclusion (q245098-quoted t)))

(defun q245098-iff-term (left right)
  (list 'if left
        (list 'if right
              (q245098-quoted t)
              (q245098-quoted nil))
        (list 'if right
              (q245098-quoted nil)
              (q245098-quoted t))))

(defun q245098-true-function (formals)
  (list 'lambda formals (q245098-quoted t)))

(defun q245098-false-function (formals)
  (list 'lambda formals (q245098-quoted nil)))

(defun q245098-booleanized-function (function formals)
  (list
   'lambda formals
   (list
    'if
    (q245098-static-apply-term function formals)
    (q245098-quoted t)
    (q245098-quoted nil))))

(defun q245098-universal-p (function formals)
  (let ((booleanized
         (q245098-booleanized-function function formals))
        (always-true (q245098-true-function formals)))
    (and (tamep-functionp function)
         (tamep-functionp booleanized)
         (tamep-functionp always-true)
         (fn-equal booleanized always-true))))

(defun q245098-exists-p (function formals)
  (let ((booleanized
         (q245098-booleanized-function function formals))
        (always-false (q245098-false-function formals)))
    (and (tamep-functionp function)
         (tamep-functionp booleanized)
         (tamep-functionp always-false)
         (not (fn-equal booleanized always-false)))))

(defun q245098-member-p (predicate object)
  (if (apply$ predicate (list object)) t nil))

(defun q245098-relation-p (relation left right)
  (if (apply$ relation (list left right)) t nil))

(defun q245098-value (function object)
  (apply$ function (list object)))

(defun q245098-le-p (relation left right)
  (q245098-relation-p relation left right))

(defun q245098-lt-p (relation left right)
  (and
   (q245098-le-p relation left right)
   (not (q245098-le-p relation right left))))

;; Arbitrary represented subsets.

(defun q245098-valid-set-row-function (carrier set)
  (list
   'lambda '(x)
   (q245098-implies-term
    (q245098-static-apply-term set '(x))
    (q245098-static-apply-term carrier '(x)))))

(defun q245098-valid-set-p (carrier set)
  (and
   (tamep-functionp set)
   (q245098-universal-p
    (q245098-valid-set-row-function carrier set)
    '(x))))

(defun q245098-subset-row-function (carrier left right)
  (list
   'lambda '(x)
   (q245098-implies-term
    (q245098-and-terms
     (list
      (q245098-static-apply-term carrier '(x))
      (q245098-static-apply-term left '(x))))
    (q245098-static-apply-term right '(x)))))

(defun q245098-subset-p (carrier left right)
  (and
   (q245098-valid-set-p carrier left)
   (q245098-valid-set-p carrier right)
   (q245098-universal-p
    (q245098-subset-row-function carrier left right)
    '(x))))

(defun q245098-intersection-term (left-term right-term)
  (list
   'lambda '(x)
   (q245098-and-terms
    (list
     (q245098-apply-term left-term '(x))
     (q245098-apply-term right-term '(x))))))

(defun q245098-set-nonempty-row-function (carrier set)
  (list
   'lambda '(x)
   (q245098-and-terms
    (list
     (q245098-static-apply-term carrier '(x))
     (q245098-static-apply-term set '(x))))))

(defun q245098-set-nonempty-p (carrier set)
  (and
   (q245098-valid-set-p carrier set)
   (q245098-exists-p
    (q245098-set-nonempty-row-function carrier set)
    '(x))))

;; Linear orders.

(defun q245098-order-reflexive-row-function (carrier le)
  (list
   'lambda '(x)
   (q245098-implies-term
    (q245098-static-apply-term carrier '(x))
    (q245098-static-apply-term le '(x x)))))

(defun q245098-order-antisymmetric-row-function (carrier le)
  (list
   'lambda '(x y)
   (q245098-implies-term
    (q245098-and-terms
     (list
      (q245098-static-apply-term carrier '(x))
      (q245098-static-apply-term carrier '(y))
      (q245098-static-apply-term le '(x y))
      (q245098-static-apply-term le '(y x))))
    (list 'equal 'x 'y))))

(defun q245098-order-transitive-row-function (carrier le)
  (list
   'lambda '(x y z)
   (q245098-implies-term
    (q245098-and-terms
     (list
      (q245098-static-apply-term carrier '(x))
      (q245098-static-apply-term carrier '(y))
      (q245098-static-apply-term carrier '(z))
      (q245098-static-apply-term le '(x y))
      (q245098-static-apply-term le '(y z))))
    (q245098-static-apply-term le '(x z)))))

(defun q245098-order-total-row-function (carrier le)
  (list
   'lambda '(x y)
   (q245098-implies-term
    (q245098-and-terms
     (list
      (q245098-static-apply-term carrier '(x))
      (q245098-static-apply-term carrier '(y))))
    (list 'if
          (q245098-static-apply-term le '(x y))
          (q245098-quoted t)
          (q245098-static-apply-term le '(y x))))))

(defun q245098-linear-order-p (carrier le)
  (and
   (tamep-functionp carrier)
   (tamep-functionp le)
   (q245098-universal-p
    (q245098-order-reflexive-row-function carrier le)
    '(x))
   (q245098-universal-p
    (q245098-order-antisymmetric-row-function carrier le)
    '(x y))
   (q245098-universal-p
    (q245098-order-transitive-row-function carrier le)
    '(x y z))
   (q245098-universal-p
    (q245098-order-total-row-function carrier le)
    '(x y))))

;; Density and conditional completeness of the domain order.

(defun q245098-between-witness-function (carrier le left right)
  (list
   'lambda '(middle)
   (q245098-and-terms
    (list
     (q245098-static-apply-term carrier '(middle))
     (list 'q245098-lt-p
           (q245098-quoted le)
           (q245098-quoted left)
           'middle)
     (list 'q245098-lt-p
           (q245098-quoted le)
           'middle
           (q245098-quoted right))))))

(defun q245098-density-row-function (carrier le)
  (list
   'lambda '(left right)
   (q245098-implies-term
    (q245098-and-terms
     (list
      (q245098-static-apply-term carrier '(left))
      (q245098-static-apply-term carrier '(right))
      (list 'q245098-lt-p
            (q245098-quoted le)
            'left
            'right)))
    (list 'q245098-exists-p
          (list 'q245098-between-witness-function
                (q245098-quoted carrier)
                (q245098-quoted le)
                'left
                'right)
          (q245098-quoted '(middle))))))

(defun q245098-dense-order-p (carrier le)
  (q245098-universal-p
   (q245098-density-row-function carrier le)
   '(left right)))

(defun q245098-upper-bound-row-function
    (carrier le set upper)
  (list
   'lambda '(x)
   (q245098-implies-term
    (q245098-and-terms
     (list
      (q245098-static-apply-term carrier '(x))
      (q245098-static-apply-term set '(x))))
    (q245098-static-apply-term
     le (list 'x (q245098-quoted upper))))))

(defun q245098-upper-bound-p
    (carrier le set upper)
  (and
   (q245098-member-p carrier upper)
   (q245098-valid-set-p carrier set)
   (q245098-universal-p
    (q245098-upper-bound-row-function
     carrier le set upper)
    '(x))))

(defun q245098-lower-bound-row-function
    (carrier le set lower)
  (list
   'lambda '(x)
   (q245098-implies-term
    (q245098-and-terms
     (list
      (q245098-static-apply-term carrier '(x))
      (q245098-static-apply-term set '(x))))
    (q245098-static-apply-term
     le (list (q245098-quoted lower) 'x)))))

(defun q245098-lower-bound-p
    (carrier le set lower)
  (and
   (q245098-member-p carrier lower)
   (q245098-valid-set-p carrier set)
   (q245098-universal-p
    (q245098-lower-bound-row-function
     carrier le set lower)
    '(x))))

(defun q245098-bounded-above-witness-function
    (carrier le set)
  (list
   'lambda '(upper)
   (list 'q245098-upper-bound-p
         (q245098-quoted carrier)
         (q245098-quoted le)
         (q245098-quoted set)
         'upper)))

(defun q245098-bounded-above-p (carrier le set)
  (q245098-exists-p
   (q245098-bounded-above-witness-function
    carrier le set)
   '(upper)))

(defun q245098-bounded-below-witness-function
    (carrier le set)
  (list
   'lambda '(lower)
   (list 'q245098-lower-bound-p
         (q245098-quoted carrier)
         (q245098-quoted le)
         (q245098-quoted set)
         'lower)))

(defun q245098-bounded-below-p (carrier le set)
  (q245098-exists-p
   (q245098-bounded-below-witness-function
    carrier le set)
   '(lower)))

(defun q245098-least-upper-bound-row-function
    (carrier le set supremum)
  (list
   'lambda '(upper)
   (q245098-implies-term
    (list 'q245098-upper-bound-p
          (q245098-quoted carrier)
          (q245098-quoted le)
          (q245098-quoted set)
          'upper)
    (q245098-static-apply-term
     le (list (q245098-quoted supremum) 'upper)))))

(defun q245098-least-upper-bound-p
    (carrier le set supremum)
  (and
   (q245098-upper-bound-p carrier le set supremum)
   (q245098-universal-p
    (q245098-least-upper-bound-row-function
     carrier le set supremum)
    '(upper))))

(defun q245098-greatest-lower-bound-row-function
    (carrier le set infimum)
  (list
   'lambda '(lower)
   (q245098-implies-term
    (list 'q245098-lower-bound-p
          (q245098-quoted carrier)
          (q245098-quoted le)
          (q245098-quoted set)
          'lower)
    (q245098-static-apply-term
     le (list 'lower (q245098-quoted infimum))))))

(defun q245098-greatest-lower-bound-p
    (carrier le set infimum)
  (and
   (q245098-lower-bound-p carrier le set infimum)
   (q245098-universal-p
    (q245098-greatest-lower-bound-row-function
     carrier le set infimum)
    '(lower))))

(defun q245098-supremum-witness-function
    (carrier le set)
  (list
   'lambda '(supremum)
   (list 'q245098-least-upper-bound-p
         (q245098-quoted carrier)
         (q245098-quoted le)
         (q245098-quoted set)
         'supremum)))

(defun q245098-infimum-witness-function
    (carrier le set)
  (list
   'lambda '(infimum)
   (list 'q245098-greatest-lower-bound-p
         (q245098-quoted carrier)
         (q245098-quoted le)
         (q245098-quoted set)
         'infimum)))

(defun q245098-has-supremum-p (carrier le set)
  (q245098-exists-p
   (q245098-supremum-witness-function
    carrier le set)
   '(supremum)))

(defun q245098-has-infimum-p (carrier le set)
  (q245098-exists-p
   (q245098-infimum-witness-function
    carrier le set)
   '(infimum)))

(defun q245098-completeness-row-function (carrier le)
  (list
   'lambda '(set)
   (q245098-and-terms
    (list
     (q245098-implies-term
      (q245098-and-terms
       (list
        (list 'q245098-valid-set-p
              (q245098-quoted carrier) 'set)
        (list 'q245098-set-nonempty-p
              (q245098-quoted carrier) 'set)
        (list 'q245098-bounded-above-p
              (q245098-quoted carrier)
              (q245098-quoted le)
              'set)))
      (list 'q245098-has-supremum-p
            (q245098-quoted carrier)
            (q245098-quoted le)
            'set))
     (q245098-implies-term
      (q245098-and-terms
       (list
        (list 'q245098-valid-set-p
              (q245098-quoted carrier) 'set)
        (list 'q245098-set-nonempty-p
              (q245098-quoted carrier) 'set)
        (list 'q245098-bounded-below-p
              (q245098-quoted carrier)
              (q245098-quoted le)
              'set)))
      (list 'q245098-has-infimum-p
            (q245098-quoted carrier)
            (q245098-quoted le)
            'set))))))

(defun q245098-conditionally-complete-order-p
    (carrier le)
  (and
   (q245098-linear-order-p carrier le)
   (q245098-set-nonempty-p carrier carrier)
   (q245098-universal-p
    (q245098-completeness-row-function carrier le)
    '(set))))

;; Neighborhood-system presentation of the codomain topology.

(defun q245098-neighborhood-welltyped-row-function
    (carrier neighborhood)
  (list
   'lambda '(x set)
   (q245098-implies-term
    (q245098-static-apply-term neighborhood '(x set))
    (q245098-and-terms
     (list
      (q245098-static-apply-term carrier '(x))
      (list 'q245098-valid-set-p
            (q245098-quoted carrier)
            'set))))))

(defun q245098-neighborhood-full-row-function
    (carrier neighborhood)
  (list
   'lambda '(x)
   (q245098-implies-term
    (q245098-static-apply-term carrier '(x))
    (q245098-static-apply-term
     neighborhood
     (list 'x (q245098-quoted carrier))))))

(defun q245098-neighborhood-member-row-function
    (carrier neighborhood)
  (list
   'lambda '(x set)
   (q245098-implies-term
    (q245098-and-terms
     (list
      (q245098-static-apply-term carrier '(x))
      (q245098-static-apply-term neighborhood '(x set))))
    (q245098-apply-term 'set '(x)))))

(defun q245098-neighborhood-intersection-row-function
    (carrier neighborhood)
  (list
   'lambda '(x left right)
   (q245098-implies-term
    (q245098-and-terms
     (list
      (q245098-static-apply-term carrier '(x))
      (q245098-static-apply-term neighborhood '(x left))
      (q245098-static-apply-term neighborhood '(x right))))
    (q245098-static-apply-term
     neighborhood
     (list
      'x
      (q245098-intersection-term 'left 'right))))))

(defun q245098-neighborhood-upward-row-function
    (carrier neighborhood)
  (list
   'lambda '(x small large)
   (q245098-implies-term
    (q245098-and-terms
     (list
      (q245098-static-apply-term carrier '(x))
      (q245098-static-apply-term neighborhood '(x small))
      (list 'q245098-subset-p
            (q245098-quoted carrier)
            'small
            'large)))
    (q245098-static-apply-term
     neighborhood '(x large)))))

(defun q245098-neighborhood-local-row-function
    (carrier neighborhood refinement set)
  (list
   'lambda '(y)
   (q245098-implies-term
    (q245098-and-terms
     (list
      (q245098-static-apply-term carrier '(y))
      (q245098-static-apply-term refinement '(y))))
    (q245098-static-apply-term
     neighborhood
     (list 'y (q245098-quoted set))))))

(defun q245098-neighborhood-local-witness-function
    (carrier neighborhood x set)
  (list
   'lambda '(refinement)
   (q245098-and-terms
    (list
     (list 'q245098-valid-set-p
           (q245098-quoted carrier)
           'refinement)
     (q245098-static-apply-term
      neighborhood
      (list (q245098-quoted x) 'refinement))
     (list 'q245098-universal-p
           (list 'q245098-neighborhood-local-row-function
                 (q245098-quoted carrier)
                 (q245098-quoted neighborhood)
                 'refinement
                 (q245098-quoted set))
           (q245098-quoted '(y)))))))

(defun q245098-neighborhood-locality-row-function
    (carrier neighborhood)
  (list
   'lambda '(x set)
   (q245098-implies-term
    (q245098-static-apply-term neighborhood '(x set))
    (list 'q245098-exists-p
          (list 'q245098-neighborhood-local-witness-function
                (q245098-quoted carrier)
                (q245098-quoted neighborhood)
                'x
                'set)
          (q245098-quoted '(refinement))))))

(defun q245098-neighborhood-space-p
    (carrier neighborhood)
  (and
   (tamep-functionp carrier)
   (tamep-functionp neighborhood)
   (q245098-universal-p
    (q245098-neighborhood-welltyped-row-function
     carrier neighborhood)
    '(x set))
   (q245098-universal-p
    (q245098-neighborhood-full-row-function
     carrier neighborhood)
    '(x))
   (q245098-universal-p
    (q245098-neighborhood-member-row-function
     carrier neighborhood)
    '(x set))
   (q245098-universal-p
    (q245098-neighborhood-intersection-row-function
     carrier neighborhood)
    '(x left right))
   (q245098-universal-p
    (q245098-neighborhood-upward-row-function
     carrier neighborhood)
    '(x small large))
   (q245098-universal-p
    (q245098-neighborhood-locality-row-function
     carrier neighborhood)
    '(x set))))

;; Closedness of the codomain order relation.

(defun q245098-separated-pair-row-function
    (carrier le left right)
  (list
   'lambda '(u v)
   (q245098-implies-term
    (q245098-and-terms
     (list
      (q245098-static-apply-term carrier '(u))
      (q245098-static-apply-term carrier '(v))
      (q245098-static-apply-term left '(u))
      (q245098-static-apply-term right '(v))))
    (q245098-not-term
     (q245098-static-apply-term le '(u v))))))

(defun q245098-order-separation-witness-function
    (carrier le neighborhood x y)
  (list
   'lambda '(left right)
   (q245098-and-terms
    (list
     (list 'q245098-valid-set-p
           (q245098-quoted carrier)
           'left)
     (list 'q245098-valid-set-p
           (q245098-quoted carrier)
           'right)
     (q245098-static-apply-term
      neighborhood
      (list (q245098-quoted x) 'left))
     (q245098-static-apply-term
      neighborhood
      (list (q245098-quoted y) 'right))
     (list 'q245098-universal-p
           (list 'q245098-separated-pair-row-function
                 (q245098-quoted carrier)
                 (q245098-quoted le)
                 'left
                 'right)
           (q245098-quoted '(u v)))))))

(defun q245098-order-closed-row-function
    (carrier le neighborhood)
  (list
   'lambda '(x y)
   (q245098-implies-term
    (q245098-and-terms
     (list
      (q245098-static-apply-term carrier '(x))
      (q245098-static-apply-term carrier '(y))
      (q245098-not-term
       (q245098-static-apply-term le '(x y)))))
    (list 'q245098-exists-p
          (list 'q245098-order-separation-witness-function
                (q245098-quoted carrier)
                (q245098-quoted le)
                (q245098-quoted neighborhood)
                'x
                'y)
          (q245098-quoted '(left right))))))

(defun q245098-order-closed-topology-p
    (carrier le neighborhood)
  (and
   (q245098-linear-order-p carrier le)
   (q245098-neighborhood-space-p carrier neighborhood)
   (q245098-universal-p
    (q245098-order-closed-row-function
     carrier le neighborhood)
    '(x y))))

;; The order-topology neighborhood basis on the domain.

(defun q245098-order-basic-subset-row-function
    (carrier le set has-lower lower has-upper upper)
  (list
   'lambda '(y)
   (q245098-implies-term
    (q245098-and-terms
     (list
      (q245098-static-apply-term carrier '(y))
      (q245098-implies-term
       (q245098-quoted has-lower)
       (list 'q245098-lt-p
             (q245098-quoted le)
             (q245098-quoted lower)
             'y))
      (q245098-implies-term
       (q245098-quoted has-upper)
       (list 'q245098-lt-p
             (q245098-quoted le)
             'y
             (q245098-quoted upper)))))
    (q245098-static-apply-term set '(y)))))

(defun q245098-order-neighborhood-witness-function
    (carrier le x set)
  (list
   'lambda '(has-lower lower has-upper upper)
   (q245098-and-terms
    (list
     (list 'booleanp 'has-lower)
     (list 'booleanp 'has-upper)
     (q245098-implies-term
      'has-lower
      (q245098-and-terms
       (list
        (q245098-static-apply-term carrier '(lower))
        (list 'q245098-lt-p
              (q245098-quoted le)
              'lower
              (q245098-quoted x)))))
     (q245098-implies-term
      'has-upper
      (q245098-and-terms
       (list
        (q245098-static-apply-term carrier '(upper))
        (list 'q245098-lt-p
              (q245098-quoted le)
              (q245098-quoted x)
              'upper))))
     (list 'q245098-universal-p
           (list 'q245098-order-basic-subset-row-function
                 (q245098-quoted carrier)
                 (q245098-quoted le)
                 (q245098-quoted set)
                 'has-lower
                 'lower
                 'has-upper
                 'upper)
           (q245098-quoted '(y)))))))

(defun q245098-order-neighborhood-p
    (carrier le x set)
  (and
   (q245098-member-p carrier x)
   (q245098-valid-set-p carrier set)
   (q245098-exists-p
    (q245098-order-neighborhood-witness-function
     carrier le x set)
    '(has-lower lower has-upper upper))))

;; Functions and continuity on the source closed interval.

(defun q245098-function-values-row-function
    (domain codomain function)
  (list
   'lambda '(x)
   (q245098-implies-term
    (q245098-static-apply-term domain '(x))
    (q245098-static-apply-term
     codomain
     (list (q245098-static-apply-term function '(x)))))))

(defun q245098-function-p
    (domain codomain function)
  (and
   (tamep-functionp function)
   (q245098-universal-p
    (q245098-function-values-row-function
     domain codomain function)
    '(x))))

(defun q245098-in-icc-p (carrier le a b x)
  (and
   (q245098-member-p carrier x)
   (q245098-le-p le a x)
   (q245098-le-p le x b)))

(defun q245098-continuity-image-row-function
    (alpha alpha-le function a b target
           has-lower lower has-upper upper)
  (list
   'lambda '(y)
   (q245098-implies-term
    (q245098-and-terms
     (list
      (q245098-static-apply-term alpha '(y))
      (q245098-static-apply-term
       alpha-le (list (q245098-quoted a) 'y))
      (q245098-static-apply-term
       alpha-le (list 'y (q245098-quoted b)))
      (q245098-implies-term
       (q245098-quoted has-lower)
       (list 'q245098-lt-p
             (q245098-quoted alpha-le)
             (q245098-quoted lower)
             'y))
      (q245098-implies-term
       (q245098-quoted has-upper)
       (list 'q245098-lt-p
             (q245098-quoted alpha-le)
             'y
             (q245098-quoted upper)))))
    (q245098-static-apply-term
     target
     (list (q245098-static-apply-term function '(y)))))))

(defun q245098-continuity-witness-function
    (alpha alpha-le function a b x target)
  (list
   'lambda '(has-lower lower has-upper upper)
   (q245098-and-terms
    (list
     (list 'booleanp 'has-lower)
     (list 'booleanp 'has-upper)
     (q245098-implies-term
      'has-lower
      (q245098-and-terms
       (list
        (q245098-static-apply-term alpha '(lower))
        (list 'q245098-lt-p
              (q245098-quoted alpha-le)
              'lower
              (q245098-quoted x)))))
     (q245098-implies-term
      'has-upper
      (q245098-and-terms
       (list
        (q245098-static-apply-term alpha '(upper))
        (list 'q245098-lt-p
              (q245098-quoted alpha-le)
              (q245098-quoted x)
              'upper))))
     (list 'q245098-universal-p
           (list 'q245098-continuity-image-row-function
                 (q245098-quoted alpha)
                 (q245098-quoted alpha-le)
                 (q245098-quoted function)
                 (q245098-quoted a)
                 (q245098-quoted b)
                 (q245098-quoted target)
                 'has-lower
                 'lower
                 'has-upper
                 'upper)
           (q245098-quoted '(y)))))))

(defun q245098-continuity-target-row-function
    (alpha alpha-le delta-neighborhood
           function a b x)
  (list
   'lambda '(target)
   (q245098-implies-term
    (q245098-static-apply-term
     delta-neighborhood
     (list
      (q245098-static-apply-term
       function (list (q245098-quoted x)))
      'target))
    (list 'q245098-exists-p
          (list 'q245098-continuity-witness-function
                (q245098-quoted alpha)
                (q245098-quoted alpha-le)
                (q245098-quoted function)
                (q245098-quoted a)
                (q245098-quoted b)
                (q245098-quoted x)
                'target)
          (q245098-quoted
           '(has-lower lower has-upper upper))))))

(defun q245098-continuity-point-row-function
    (alpha alpha-le delta-neighborhood function a b)
  (list
   'lambda '(x)
   (q245098-implies-term
    (q245098-and-terms
     (list
      (q245098-static-apply-term alpha '(x))
      (q245098-static-apply-term
       alpha-le (list (q245098-quoted a) 'x))
      (q245098-static-apply-term
       alpha-le (list 'x (q245098-quoted b)))))
    (list 'q245098-universal-p
          (list 'q245098-continuity-target-row-function
                (q245098-quoted alpha)
                (q245098-quoted alpha-le)
                (q245098-quoted delta-neighborhood)
                (q245098-quoted function)
                (q245098-quoted a)
                (q245098-quoted b)
                'x)
          (q245098-quoted '(target))))))

(defun q245098-continuous-on-icc-p
    (alpha alpha-le delta-neighborhood function a b)
  (q245098-universal-p
   (q245098-continuity-point-row-function
    alpha alpha-le delta-neighborhood function a b)
   '(x)))

;; The image inclusion conclusion, with both quantifiers internal.

(defun q245098-image-witness-function
    (alpha alpha-le function a b target)
  (list
   'lambda '(x)
   (q245098-and-terms
    (list
     (q245098-static-apply-term alpha '(x))
     (q245098-static-apply-term
      alpha-le (list (q245098-quoted a) 'x))
     (q245098-static-apply-term
      alpha-le (list 'x (q245098-quoted b)))
     (list 'equal
           (q245098-static-apply-term function '(x))
           (q245098-quoted target))))))

(defun q245098-intermediate-value-row-function
    (delta delta-le function alpha alpha-le a b)
  (list
   'lambda '(target)
   (q245098-implies-term
    (q245098-and-terms
     (list
      (q245098-static-apply-term delta '(target))
      (q245098-static-apply-term
       delta-le
       (list
        (q245098-static-apply-term
         function (list (q245098-quoted a)))
        'target))
      (q245098-static-apply-term
       delta-le
       (list
        'target
        (q245098-static-apply-term
         function (list (q245098-quoted b)))))))
    (list 'q245098-exists-p
          (list 'q245098-image-witness-function
                (q245098-quoted alpha)
                (q245098-quoted alpha-le)
                (q245098-quoted function)
                (q245098-quoted a)
                (q245098-quoted b)
                'target)
          (q245098-quoted '(x))))))

;; intermediate_value_Icc
(defun thousand-theorems-q245098-intermediate-value-icc-statement
    (alpha alpha-le delta delta-le delta-neighborhood f a b)
  (implies
   (and
    (q245098-conditionally-complete-order-p alpha alpha-le)
    (q245098-dense-order-p alpha alpha-le)
    (q245098-order-closed-topology-p
     delta delta-le delta-neighborhood)
    (q245098-member-p alpha a)
    (q245098-member-p alpha b)
    (q245098-le-p alpha-le a b)
    (q245098-function-p alpha delta f)
    (q245098-continuous-on-icc-p
     alpha alpha-le delta-neighborhood f a b))
   (q245098-universal-p
    (q245098-intermediate-value-row-function
     delta delta-le f alpha alpha-le a b)
    '(target))))

(value-triple :itpeval-statement-checked)
:q
