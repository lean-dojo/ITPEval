;; Statement-only formalization of thousand-theorems corpus artifact Q7432915,
;; "Schroeder-Bernstein theorem for measurable spaces": measurable embeddings
;; in both directions between arbitrary measurable spaces yield a measurable
;; equivalence. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The universe below is an extensional presentation of arbitrary sets and
;; maps.  An exact comprehension constructor represents every tame unary
;; family whose natural-number values are represented sets, so countable-union
;; closure ranges over every represented countable family.  Exact operations
;; give complement, binary union, countable union, image, and preimage.
;; Additional constructors provide the standard Schroeder-Bernstein sequence
;; and its two piecewise maps; their bijectivity and measurability are not
;; assumed.  The measurable equivalence remains existentially quantified
;; inside the final statement.

(defun q7432915-quoted (object)
  (list 'quote object))

(defun q7432915-term-list (terms)
  (if (consp terms)
      (list 'cons
            (car terms)
            (q7432915-term-list (cdr terms)))
    (q7432915-quoted nil)))

(defun q7432915-static-apply-term (function arguments)
  (list 'apply$
        (q7432915-quoted function)
        (q7432915-term-list arguments)))

(defun q7432915-and-terms (terms)
  (if (consp terms)
      (list 'if
            (car terms)
            (q7432915-and-terms (cdr terms))
            (q7432915-quoted nil))
    (q7432915-quoted t)))

(defun q7432915-not-term (term)
  (list 'if term
        (q7432915-quoted nil)
        (q7432915-quoted t)))

(defun q7432915-implies-term (hypothesis conclusion)
  (list 'if hypothesis conclusion (q7432915-quoted t)))

(defun q7432915-iff-term (left right)
  (list 'if left
        (list 'if right
              (q7432915-quoted t)
              (q7432915-quoted nil))
        (list 'if right
              (q7432915-quoted nil)
              (q7432915-quoted t))))

(defun q7432915-true-function (formals)
  (list 'lambda formals (q7432915-quoted t)))

(defun q7432915-universal-p (function formals)
  (let ((always-true (q7432915-true-function formals)))
    (and (tamep-functionp function)
         (tamep-functionp always-true)
         (fn-equal function always-true))))

;; Universe package:
;;   0  set-sort
;;   1  member
;;   2  set-difference-choice
;;   3  sequence-sort
;;   4  sequence-entry
;;   5  map-sort
;;   6  map-value
;;   7  empty-set
;;   8  complement
;;   9  countable-union
;;   10 union-member-choice
;;   11 preimage
;;   12 image
;;   13 image-member-choice
;;   14 Schroeder-Bernstein sequence constructor
;;   15 Schroeder-Bernstein forward-map constructor
;;   16 Schroeder-Bernstein inverse-map constructor
;;   17 exact sequence-comprehension constructor
;;   18 binary-union constructor

(defun q7432915-u-set-sort (u) (nth 0 u))
(defun q7432915-u-member (u) (nth 1 u))
(defun q7432915-u-set-difference-choice (u) (nth 2 u))
(defun q7432915-u-sequence-sort (u) (nth 3 u))
(defun q7432915-u-sequence-entry (u) (nth 4 u))
(defun q7432915-u-map-sort (u) (nth 5 u))
(defun q7432915-u-map-value (u) (nth 6 u))
(defun q7432915-u-empty (u) (nth 7 u))
(defun q7432915-u-complement (u) (nth 8 u))
(defun q7432915-u-union (u) (nth 9 u))
(defun q7432915-u-union-member-choice (u) (nth 10 u))
(defun q7432915-u-preimage (u) (nth 11 u))
(defun q7432915-u-image (u) (nth 12 u))
(defun q7432915-u-image-choice (u) (nth 13 u))
(defun q7432915-u-sb-sequence (u) (nth 14 u))
(defun q7432915-u-sb-forward (u) (nth 15 u))
(defun q7432915-u-sb-inverse (u) (nth 16 u))
(defun q7432915-u-sequence-comprehension (u) (nth 17 u))
(defun q7432915-u-binary-union (u) (nth 18 u))

(defun-sk q7432915-set-family-p (u family)
  (forall (n)
    (implies
     (natp n)
     (apply$
      (q7432915-u-set-sort u)
      (list (apply$ family (list n)))))))

(defun-sk q7432915-sequence-comprehension-laws-p (u)
  (forall (family n)
    (implies
     (and
      (tamep-functionp family)
      (q7432915-set-family-p u family)
      (natp n))
     (let ((sequence
            (apply$
             (q7432915-u-sequence-comprehension u)
             (list family))))
       (and
        (apply$ (q7432915-u-sequence-sort u)
                (list sequence))
        (equal
         (apply$ (q7432915-u-sequence-entry u)
                 (list sequence n))
         (apply$ family (list n))))))))

(defun q7432915-universe-set-laws-function (u)
  (let* ((set-sort (q7432915-u-set-sort u))
         (member (q7432915-u-member u))
         (difference-choice
          (q7432915-u-set-difference-choice u))
         (sequence-sort (q7432915-u-sequence-sort u))
         (sequence-entry (q7432915-u-sequence-entry u))
         (map-sort (q7432915-u-map-sort u))
         (map-value (q7432915-u-map-value u))
         (empty (q7432915-u-empty u))
         (complement (q7432915-u-complement u))
         (union (q7432915-u-union u))
         (union-choice (q7432915-u-union-member-choice u))
         (preimage (q7432915-u-preimage u))
         (image (q7432915-u-image u))
         (image-choice (q7432915-u-image-choice u))
         (binary-union (q7432915-u-binary-union u))
         (set-object
          (q7432915-static-apply-term set-sort '(set)))
         (left-object
          (q7432915-static-apply-term set-sort '(left)))
         (right-object
          (q7432915-static-apply-term set-sort '(right)))
         (domain-object
          (q7432915-static-apply-term set-sort '(domain)))
         (codomain-object
          (q7432915-static-apply-term set-sort '(codomain)))
         (sequence-object
          (q7432915-static-apply-term sequence-sort '(sequence)))
         (map-object
          (q7432915-static-apply-term map-sort '(map)))
         (set-x
          (q7432915-static-apply-term member '(set x)))
         (left-x
          (q7432915-static-apply-term member '(left x)))
         (right-x
          (q7432915-static-apply-term member '(right x)))
         (domain-x
          (q7432915-static-apply-term member '(domain x)))
         (codomain-y
          (q7432915-static-apply-term member '(codomain y)))
         (map-x
          (q7432915-static-apply-term map-value '(map x)))
         (difference
          (q7432915-static-apply-term
           difference-choice '(left right)))
         (left-difference
          (q7432915-static-apply-term
           member (list 'left difference)))
         (right-difference
          (q7432915-static-apply-term
           member (list 'right difference)))
         (complement-set
          (q7432915-static-apply-term
           complement '(domain set)))
         (binary-union-set
          (q7432915-static-apply-term
           binary-union '(domain left right)))
         (sequence-n
          (q7432915-static-apply-term
           sequence-entry '(sequence n)))
         (union-set
          (q7432915-static-apply-term union '(sequence)))
         (union-index
          (q7432915-static-apply-term
           union-choice '(sequence x)))
         (union-index-set
          (q7432915-static-apply-term
           sequence-entry (list 'sequence union-index)))
         (preimage-set
          (q7432915-static-apply-term
           preimage '(domain map set)))
         (image-set
          (q7432915-static-apply-term
           image '(domain codomain map set)))
         (chosen-x
          (q7432915-static-apply-term
           image-choice '(domain codomain map set y))))
    (list
     'lambda
     '(set left right domain codomain sequence map x y n)
     (q7432915-and-terms
      (list
       (q7432915-implies-term
        (list 'equal 'set (q7432915-quoted empty))
        (q7432915-and-terms
         (list set-object (q7432915-not-term set-x))))
       (q7432915-implies-term
        (q7432915-and-terms
         (list left-object right-object
               (q7432915-not-term
                (list 'equal 'left 'right))))
        (q7432915-not-term
         (q7432915-iff-term
          left-difference right-difference)))
       (q7432915-implies-term
        (q7432915-and-terms
         (list domain-object set-object))
        (q7432915-and-terms
         (list
          (q7432915-static-apply-term
           set-sort (list complement-set))
          (q7432915-iff-term
           (q7432915-static-apply-term
            member (list complement-set 'x))
           (q7432915-and-terms
            (list domain-x
                  (q7432915-not-term set-x)))))))
       (q7432915-implies-term
        (q7432915-and-terms
         (list domain-object left-object right-object))
        (q7432915-and-terms
         (list
          (q7432915-static-apply-term
           set-sort (list binary-union-set))
          (q7432915-iff-term
           (q7432915-static-apply-term
            member (list binary-union-set 'x))
           (q7432915-and-terms
            (list
             domain-x
             (list 'if
                   left-x
                   (q7432915-quoted t)
                   right-x)))))))
       (q7432915-implies-term
        (q7432915-and-terms
         (list sequence-object (list 'natp 'n)))
        (q7432915-static-apply-term
         set-sort (list sequence-n)))
       (q7432915-implies-term
        sequence-object
        (q7432915-static-apply-term
         set-sort (list union-set)))
       (q7432915-implies-term
        (q7432915-and-terms
         (list sequence-object
               (q7432915-static-apply-term
                member (list union-set 'x))))
        (q7432915-and-terms
         (list
          (list 'natp union-index)
          (q7432915-static-apply-term
           member (list union-index-set 'x)))))
       (q7432915-implies-term
        (q7432915-and-terms
         (list sequence-object
               (list 'natp 'n)
               (q7432915-static-apply-term
                member (list sequence-n 'x))))
        (q7432915-static-apply-term
         member (list union-set 'x)))
       (q7432915-implies-term
        (q7432915-and-terms
         (list domain-object set-object map-object))
        (q7432915-and-terms
         (list
          (q7432915-static-apply-term
           set-sort (list preimage-set))
          (q7432915-iff-term
           (q7432915-static-apply-term
            member (list preimage-set 'x))
           (q7432915-and-terms
            (list
             domain-x
             (q7432915-static-apply-term
              member (list 'set map-x))))))))
       (q7432915-implies-term
        (q7432915-and-terms
         (list domain-object codomain-object
               set-object map-object))
        (q7432915-and-terms
         (list
          (q7432915-static-apply-term
           set-sort (list image-set))
          (q7432915-implies-term
           (q7432915-static-apply-term
            member (list image-set 'y))
           (q7432915-and-terms
            (list
             codomain-y
             (q7432915-static-apply-term
              member (list 'domain chosen-x))
             (q7432915-static-apply-term
              member (list 'set chosen-x))
             (list 'equal
                   (q7432915-static-apply-term
                    map-value (list 'map chosen-x))
                   'y))))
          (q7432915-implies-term
           (q7432915-and-terms
            (list
             domain-x set-x
             (q7432915-static-apply-term
              member (list 'codomain map-x))))
           (q7432915-static-apply-term
            member (list image-set map-x)))))))))))

(defun q7432915-universe-sb-laws-function (u)
  (let* ((set-sort (q7432915-u-set-sort u))
         (member (q7432915-u-member u))
         (sequence-sort (q7432915-u-sequence-sort u))
         (sequence-entry (q7432915-u-sequence-entry u))
         (map-sort (q7432915-u-map-sort u))
         (map-value (q7432915-u-map-value u))
         (complement (q7432915-u-complement u))
         (image (q7432915-u-image u))
         (image-choice (q7432915-u-image-choice u))
         (sb-sequence (q7432915-u-sb-sequence u))
         (sb-forward (q7432915-u-sb-forward u))
         (sb-inverse (q7432915-u-sb-inverse u))
         (alpha-object
          (q7432915-static-apply-term set-sort '(alpha)))
         (beta-object
          (q7432915-static-apply-term set-sort '(beta)))
         (f-object
          (q7432915-static-apply-term map-sort '(f)))
         (g-object
          (q7432915-static-apply-term map-sort '(g)))
         (c-object
          (q7432915-static-apply-term set-sort '(c)))
         (sequence
          (q7432915-static-apply-term
           sb-sequence '(alpha beta f g)))
         (entry-zero
          (q7432915-static-apply-term
           sequence-entry
           (list sequence (q7432915-quoted 0))))
         (entry-n
          (q7432915-static-apply-term
           sequence-entry (list sequence 'n)))
         (entry-next
          (q7432915-static-apply-term
           sequence-entry
           (list sequence
                 (list 'binary-+ 'n (q7432915-quoted 1)))))
         (g-range
          (q7432915-static-apply-term
           image '(beta alpha g beta)))
         (base
          (q7432915-static-apply-term
           complement (list 'alpha g-range)))
         (f-image-entry
          (q7432915-static-apply-term
           image (list 'alpha 'beta 'f entry-n)))
         (step
          (q7432915-static-apply-term
           image (list 'beta 'alpha 'g f-image-entry)))
         (forward
          (q7432915-static-apply-term
           sb-forward '(alpha beta f g c)))
         (inverse
          (q7432915-static-apply-term
           sb-inverse '(alpha beta f g c)))
         (f-x
          (q7432915-static-apply-term map-value '(f x)))
         (g-y
          (q7432915-static-apply-term map-value '(g y)))
         (g-preimage-x
          (q7432915-static-apply-term
           image-choice '(beta alpha g beta x)))
         (f-preimage-y
          (q7432915-static-apply-term
           image-choice '(alpha beta f c y))))
    (list
     'lambda '(alpha beta f g c x y n)
     (q7432915-implies-term
      (q7432915-and-terms
       (list alpha-object beta-object f-object g-object))
      (q7432915-and-terms
       (list
        (q7432915-static-apply-term
         sequence-sort (list sequence))
        (list 'equal entry-zero base)
        (q7432915-implies-term
         (list 'natp 'n)
         (list 'equal entry-next step))
        (q7432915-implies-term
         c-object
         (q7432915-and-terms
          (list
           (q7432915-static-apply-term
            map-sort (list forward))
           (q7432915-static-apply-term
            map-sort (list inverse))
           (q7432915-implies-term
            (q7432915-static-apply-term
             member '(alpha x))
            (list
             'equal
             (q7432915-static-apply-term
              map-value (list forward 'x))
             (list
              'if
              (q7432915-static-apply-term
               member '(c x))
              f-x
              g-preimage-x)))
           (q7432915-implies-term
            (q7432915-static-apply-term
             member '(beta y))
            (list
             'equal
             (q7432915-static-apply-term
              map-value (list inverse 'y))
             (list
              'if
              (q7432915-static-apply-term
               member (list 'c g-y))
              f-preimage-y
              g-y))))))))))))

(defun q7432915-universe-p (u)
  (and
   (true-listp u)
   (equal (len u) 19)
   (tamep-functionp (q7432915-u-set-sort u))
   (tamep-functionp (q7432915-u-member u))
   (tamep-functionp
    (q7432915-u-set-difference-choice u))
   (tamep-functionp (q7432915-u-sequence-sort u))
   (tamep-functionp (q7432915-u-sequence-entry u))
   (tamep-functionp (q7432915-u-map-sort u))
   (tamep-functionp (q7432915-u-map-value u))
   (tamep-functionp (q7432915-u-complement u))
   (tamep-functionp (q7432915-u-union u))
   (tamep-functionp
    (q7432915-u-union-member-choice u))
   (tamep-functionp (q7432915-u-preimage u))
   (tamep-functionp (q7432915-u-image u))
   (tamep-functionp (q7432915-u-image-choice u))
   (tamep-functionp (q7432915-u-sb-sequence u))
   (tamep-functionp (q7432915-u-sb-forward u))
   (tamep-functionp (q7432915-u-sb-inverse u))
   (tamep-functionp
    (q7432915-u-sequence-comprehension u))
   (tamep-functionp (q7432915-u-binary-union u))
   (q7432915-universal-p
    (q7432915-u-sequence-sort u)
    '(sequence))
   (q7432915-universal-p
    (q7432915-u-map-sort u)
    '(map))
   (q7432915-universal-p
    (q7432915-universe-set-laws-function u)
    '(set left right domain codomain sequence map x y n))
   (q7432915-universal-p
    (q7432915-universe-sb-laws-function u)
    '(alpha beta f g c x y n))
   (q7432915-sequence-comprehension-laws-p u)))

;; A measurable-space package contains its measurable-set family and a
;; counterexample selector for countable-union closure.

(defun q7432915-sigma-family (sigma) (nth 0 sigma))
(defun q7432915-sigma-union-failure-choice (sigma) (nth 1 sigma))

(defun q7432915-sigma-laws-function (u carrier sigma)
  (let* ((set-sort (q7432915-u-set-sort u))
         (member (q7432915-u-member u))
         (sequence-sort (q7432915-u-sequence-sort u))
         (sequence-entry (q7432915-u-sequence-entry u))
         (complement (q7432915-u-complement u))
         (union (q7432915-u-union u))
         (binary-union (q7432915-u-binary-union u))
         (family (q7432915-sigma-family sigma))
         (failure
          (q7432915-sigma-union-failure-choice sigma))
         (set-measurable
          (q7432915-static-apply-term family '(set)))
         (left-measurable
          (q7432915-static-apply-term family '(left)))
         (right-measurable
          (q7432915-static-apply-term family '(right)))
         (binary-union-set
          (q7432915-static-apply-term
           binary-union
           (list (q7432915-quoted carrier) 'left 'right)))
         (sequence-object
          (q7432915-static-apply-term
           sequence-sort '(sequence)))
         (union-set
          (q7432915-static-apply-term union '(sequence)))
         (failure-index
          (q7432915-static-apply-term failure '(sequence)))
         (failure-set
          (q7432915-static-apply-term
           sequence-entry (list 'sequence failure-index))))
    (list
     'lambda '(set left right sequence x)
     (q7432915-and-terms
      (list
       (q7432915-implies-term
        set-measurable
        (q7432915-and-terms
         (list
          (q7432915-static-apply-term set-sort '(set))
          (q7432915-implies-term
           (q7432915-static-apply-term member '(set x))
           (q7432915-static-apply-term
            member (list (q7432915-quoted carrier) 'x)))
          (q7432915-static-apply-term
           family
           (list
            (q7432915-static-apply-term
             complement
             (list (q7432915-quoted carrier) 'set)))))))
       (q7432915-implies-term
        (q7432915-and-terms
         (list left-measurable right-measurable))
        (q7432915-static-apply-term
         family (list binary-union-set)))
       (q7432915-implies-term
        (q7432915-and-terms
         (list sequence-object
               (q7432915-not-term
                (q7432915-static-apply-term
                 family (list union-set)))))
        (q7432915-and-terms
         (list
          (list 'natp failure-index)
          (q7432915-not-term
           (q7432915-static-apply-term
            family (list failure-set)))))))))))

(defun q7432915-sigma-algebra-p (u carrier sigma)
  (and
   (apply$ (q7432915-u-set-sort u) (list carrier))
   (true-listp sigma)
   (equal (len sigma) 2)
   (tamep-functionp (q7432915-sigma-family sigma))
   (tamep-functionp
    (q7432915-sigma-union-failure-choice sigma))
   (apply$ (q7432915-sigma-family sigma)
           (list (q7432915-u-empty u)))
   (q7432915-universal-p
    (q7432915-sigma-laws-function u carrier sigma)
    '(set left right sequence x))))

(defun q7432915-embedding-laws-function
    (u source target source-sigma target-sigma map)
  (let* ((member (q7432915-u-member u))
         (map-value (q7432915-u-map-value u))
         (preimage (q7432915-u-preimage u))
         (image (q7432915-u-image u))
         (source-family
          (q7432915-sigma-family source-sigma))
         (target-family
          (q7432915-sigma-family target-sigma))
         (source-x
          (q7432915-static-apply-term
           member (list (q7432915-quoted source) 'x)))
         (source-y
          (q7432915-static-apply-term
           member (list (q7432915-quoted source) 'y)))
         (map-x
          (q7432915-static-apply-term
           map-value (list (q7432915-quoted map) 'x)))
         (map-y
          (q7432915-static-apply-term
           map-value (list (q7432915-quoted map) 'y)))
         (preimage-set
          (q7432915-static-apply-term
           preimage
           (list (q7432915-quoted source)
                 (q7432915-quoted map) 'set)))
         (image-set
          (q7432915-static-apply-term
           image
           (list (q7432915-quoted source)
                 (q7432915-quoted target)
                 (q7432915-quoted map) 'set))))
    (list
     'lambda '(set x y)
     (q7432915-and-terms
      (list
       (q7432915-implies-term
        source-x
        (q7432915-static-apply-term
         member (list (q7432915-quoted target) map-x)))
       (q7432915-implies-term
        (q7432915-and-terms (list source-x source-y))
        (q7432915-iff-term
         (list 'equal map-x map-y)
         (list 'equal 'x 'y)))
       (q7432915-implies-term
        (q7432915-static-apply-term target-family '(set))
        (q7432915-static-apply-term
         source-family (list preimage-set)))
       (q7432915-implies-term
        (q7432915-static-apply-term source-family '(set))
        (q7432915-static-apply-term
         target-family (list image-set))))))))

(defun q7432915-measurable-embedding-p
    (u source target source-sigma target-sigma map)
  (and
   (apply$ (q7432915-u-map-sort u) (list map))
   (q7432915-universal-p
    (q7432915-embedding-laws-function
     u source target source-sigma target-sigma map)
    '(set x y))))

(defun q7432915-measurable-equivalence-laws-function
    (u alpha beta alpha-sigma beta-sigma forward inverse)
  (let* ((member (q7432915-u-member u))
         (map-value (q7432915-u-map-value u))
         (preimage (q7432915-u-preimage u))
         (alpha-family
          (q7432915-sigma-family alpha-sigma))
         (beta-family
          (q7432915-sigma-family beta-sigma))
         (forward-x
          (q7432915-static-apply-term
           map-value (list (q7432915-quoted forward) 'x)))
         (inverse-y
          (q7432915-static-apply-term
           map-value (list (q7432915-quoted inverse) 'y)))
         (forward-preimage
          (q7432915-static-apply-term
           preimage
           (list (q7432915-quoted alpha)
                 (q7432915-quoted forward) 'set)))
         (inverse-preimage
          (q7432915-static-apply-term
           preimage
           (list (q7432915-quoted beta)
                 (q7432915-quoted inverse) 'set))))
    (list
     'lambda '(set x y)
     (q7432915-and-terms
      (list
       (q7432915-implies-term
        (q7432915-static-apply-term
         member (list (q7432915-quoted alpha) 'x))
        (q7432915-and-terms
         (list
          (q7432915-static-apply-term
           member (list (q7432915-quoted beta) forward-x))
          (list
           'equal
           (q7432915-static-apply-term
            map-value
            (list (q7432915-quoted inverse) forward-x))
           'x))))
       (q7432915-implies-term
        (q7432915-static-apply-term
         member (list (q7432915-quoted beta) 'y))
        (q7432915-and-terms
         (list
          (q7432915-static-apply-term
           member (list (q7432915-quoted alpha) inverse-y))
          (list
           'equal
           (q7432915-static-apply-term
            map-value
            (list (q7432915-quoted forward) inverse-y))
           'y))))
       (q7432915-implies-term
        (q7432915-static-apply-term beta-family '(set))
        (q7432915-static-apply-term
         alpha-family (list forward-preimage)))
       (q7432915-implies-term
        (q7432915-static-apply-term alpha-family '(set))
        (q7432915-static-apply-term
         beta-family (list inverse-preimage))))))))

(defun q7432915-measurable-equivalence-p
    (u alpha beta alpha-sigma beta-sigma forward inverse)
  (and
   (apply$ (q7432915-u-map-sort u) (list forward))
   (apply$ (q7432915-u-map-sort u) (list inverse))
   (q7432915-universal-p
    (q7432915-measurable-equivalence-laws-function
     u alpha beta alpha-sigma beta-sigma forward inverse)
    '(set x y))))

(defun-sk q7432915-measurable-equivalence-exists-p
    (u alpha beta alpha-sigma beta-sigma)
  (exists (forward inverse)
    (q7432915-measurable-equivalence-p
     u alpha beta alpha-sigma beta-sigma forward inverse)))

(defun thousand-theorems-q7432915-schroeder-bernstein-statement
    (universe alpha beta alpha-sigma beta-sigma f g)
  (implies
   (and
    (q7432915-universe-p universe)
    (q7432915-sigma-algebra-p
     universe alpha alpha-sigma)
    (q7432915-sigma-algebra-p
     universe beta beta-sigma)
    (q7432915-measurable-embedding-p
     universe alpha beta alpha-sigma beta-sigma f)
    (q7432915-measurable-embedding-p
     universe beta alpha beta-sigma alpha-sigma g))
   (q7432915-measurable-equivalence-exists-p
    universe alpha beta alpha-sigma beta-sigma)))

;; Admission-time audit: every function object supplied to FN-EQUAL is
;; APPLY$-tame.

(defun q7432915-all-reified-functions-tame-p ()
  (let* ((unary '(lambda (x) (quote nil)))
         (binary '(lambda (x y) (quote nil)))
         (ternary '(lambda (x y z) (quote nil)))
         (quaternary '(lambda (w x y z) (quote nil)))
         (quinary '(lambda (v w x y z) (quote nil)))
         (universe
          (list unary binary binary unary binary unary binary
                nil binary unary binary ternary quaternary
                quinary quaternary quinary quinary unary
                ternary))
         (sigma (list unary unary)))
    (and
     (tamep-functionp
      (q7432915-true-function '(x)))
     (tamep-functionp
      (q7432915-universe-set-laws-function universe))
     (tamep-functionp
      (q7432915-universe-sb-laws-function universe))
     (tamep-functionp
      (q7432915-sigma-laws-function universe nil sigma))
     (tamep-functionp
      (q7432915-embedding-laws-function
       universe nil nil sigma sigma nil))
     (tamep-functionp
      (q7432915-measurable-equivalence-laws-function
       universe nil nil sigma sigma nil nil)))))

(value-triple
 (if (q7432915-all-reified-functions-tame-p)
     :itpeval-tame-reified-functions-checked
   (er hard 'q7432915-tameness
       "A reified statement function is not tame.")))

(value-triple :itpeval-statement-checked)
:q
