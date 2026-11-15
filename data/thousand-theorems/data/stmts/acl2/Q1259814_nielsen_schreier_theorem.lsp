;; Statement-only formalization of thousand-theorems corpus artifact Q1259814,
;; "Nielsen–Schreier theorem": every subgroup of an arbitrary free group is
;; itself a free group. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Arbitrary carriers, operations, and subsets are tame APPLY$ function
;; objects. FN-EQUAL supplies unbounded universal quantification over ACL2
;; objects, while inequality with a constant-false function supplies internal
;; existential quantification.
;;
;; Freeness is represented by the equivalent reduced-word normal-form
;; property. The existential witness contains a basis predicate, the reduced
;; word predicate, word evaluation, and a normal-form map. A letter is a
;; two-element list (generator sign), where T is the generator and NIL is its
;; inverse. The laws say that every group element has exactly one reduced word.
;; Thus no basis, lift, or normal-form witness is exposed as a statement
;; parameter.

(defun q1259814-quoted (object)
  (list 'quote object))

(defun q1259814-term-list (terms)
  (if (consp terms)
      (list
       'cons
       (car terms)
       (q1259814-term-list (cdr terms)))
    (q1259814-quoted nil)))

(defun q1259814-apply-term (function-term arguments)
  (list
   'apply$
   function-term
   (q1259814-term-list arguments)))

(defun q1259814-static-apply-term (function arguments)
  (q1259814-apply-term
   (q1259814-quoted function)
   arguments))

(defun q1259814-and-terms (terms)
  (if (consp terms)
      (list
       'if
       (car terms)
       (q1259814-and-terms (cdr terms))
       (q1259814-quoted nil))
    (q1259814-quoted t)))

(defun q1259814-or-terms (terms)
  (if (consp terms)
      (list
       'if
       (car terms)
       (q1259814-quoted t)
       (q1259814-or-terms (cdr terms)))
    (q1259814-quoted nil)))

(defun q1259814-not-term (term)
  (list
   'if
   term
   (q1259814-quoted nil)
   (q1259814-quoted t)))

(defun q1259814-implies-term (hypothesis conclusion)
  (list
   'if
   hypothesis
   conclusion
   (q1259814-quoted t)))

(defun q1259814-iff-term (left right)
  (list
   'if
   left
   (list
    'if
    right
    (q1259814-quoted t)
    (q1259814-quoted nil))
   (list
    'if
    right
    (q1259814-quoted nil)
    (q1259814-quoted t))))

(defun q1259814-nth-term (index tuple)
  (list 'nth (q1259814-quoted index) tuple))

(defun q1259814-tuple-of-length-term (tuple length)
  (q1259814-and-terms
   (list
    (list 'true-listp tuple)
    (list
     'equal
     (list 'len tuple)
     (q1259814-quoted length)))))

(defun q1259814-true-function (formals)
  (list 'lambda formals (q1259814-quoted t)))

(defun q1259814-false-function (formals)
  (list 'lambda formals (q1259814-quoted nil)))

(defun q1259814-universal-p (condition formals)
  (let ((always-true
         (q1259814-true-function formals)))
    (and
     (tamep-functionp condition)
     (tamep-functionp always-true)
     (fn-equal condition always-true))))

(defun q1259814-exists-p (condition formals)
  (let ((always-false
         (q1259814-false-function formals)))
    (and
     (tamep-functionp condition)
     (tamep-functionp always-false)
     (not (fn-equal condition always-false)))))

(defun q1259814-member-p (predicate object)
  (if (apply$ predicate (list object))
      t
    nil))

(defun q1259814-member-term (predicate-term object)
  (q1259814-apply-term predicate-term (list object)))

(defun q1259814-mul-term (multiplication-term left right)
  (q1259814-apply-term multiplication-term (list left right)))

(defun q1259814-inv-term (inverse-term object)
  (q1259814-apply-term inverse-term (list object)))

;; Group and subgroup structures on arbitrary, potentially infinite carriers.

(defun q1259814-group-laws-function
    (carrier multiplication inverse identity)
  (let* ((x (q1259814-nth-term 0 'tuple))
         (y (q1259814-nth-term 1 'tuple))
         (z (q1259814-nth-term 2 'tuple))
         (x-in
          (q1259814-static-apply-term carrier (list x)))
         (y-in
          (q1259814-static-apply-term carrier (list y)))
         (z-in
          (q1259814-static-apply-term carrier (list z)))
         (inv-x
          (q1259814-static-apply-term inverse (list x)))
         (xy
          (q1259814-static-apply-term
           multiplication
           (list x y)))
         (unary-hypothesis
          (q1259814-and-terms
           (list
            (q1259814-tuple-of-length-term 'tuple 1)
            x-in)))
         (binary-hypothesis
          (q1259814-and-terms
           (list
            (q1259814-tuple-of-length-term 'tuple 2)
            x-in
            y-in)))
         (ternary-hypothesis
          (q1259814-and-terms
           (list
            (q1259814-tuple-of-length-term 'tuple 3)
            x-in
            y-in
            z-in))))
    (list
     'lambda
     '(tuple)
     (q1259814-and-terms
      (list
       (q1259814-implies-term
        unary-hypothesis
        (q1259814-and-terms
         (list
          (q1259814-static-apply-term carrier (list inv-x))
          (list
           'equal
           (q1259814-static-apply-term
            multiplication
            (list x (q1259814-quoted identity)))
           x)
          (list
           'equal
           (q1259814-static-apply-term
            multiplication
            (list (q1259814-quoted identity) x))
           x)
          (list
           'equal
           (q1259814-static-apply-term
            multiplication
            (list x inv-x))
           (q1259814-quoted identity))
          (list
           'equal
           (q1259814-static-apply-term
            multiplication
            (list inv-x x))
           (q1259814-quoted identity)))))
       (q1259814-implies-term
        binary-hypothesis
        (q1259814-static-apply-term carrier (list xy)))
       (q1259814-implies-term
        ternary-hypothesis
        (list
         'equal
         (q1259814-static-apply-term
          multiplication
          (list
           (q1259814-static-apply-term
            multiplication
            (list x y))
           z))
         (q1259814-static-apply-term
          multiplication
          (list
           x
           (q1259814-static-apply-term
            multiplication
            (list y z)))))))))))

(defun q1259814-group-p
    (carrier multiplication inverse identity)
  (and
   (tamep-functionp carrier)
   (tamep-functionp multiplication)
   (tamep-functionp inverse)
   (q1259814-member-p carrier identity)
   (q1259814-universal-p
    (q1259814-group-laws-function
     carrier multiplication inverse identity)
    '(tuple))))

(defun q1259814-subset-function (left right)
  (list
   'lambda
   '(x)
   (q1259814-implies-term
    (q1259814-static-apply-term left '(x))
    (q1259814-static-apply-term right '(x)))))

(defun q1259814-subset-p (left right)
  (and
   (tamep-functionp left)
   (tamep-functionp right)
   (q1259814-universal-p
    (q1259814-subset-function left right)
    '(x))))

(defun q1259814-subgroup-p
    (carrier multiplication inverse identity subgroup)
  (and
   (q1259814-group-p
    carrier multiplication inverse identity)
   (q1259814-subset-p subgroup carrier)
   (q1259814-group-p
    subgroup multiplication inverse identity)))

;; The following marker is used only while constructing a reified function
;; object. It inserts a runtime term into an otherwise quoted syntax tree.

(defun q1259814-runtime-node (term)
  (list :q1259814-runtime term))

(defun q1259814-runtime-node-p (tree)
  (and
   (true-listp tree)
   (equal (len tree) 2)
   (equal (car tree) :q1259814-runtime)))

(defun q1259814-dynamic-tree-term (tree)
  (if (q1259814-runtime-node-p tree)
      (cadr tree)
    (if (consp tree)
        (list
         'cons
         (q1259814-dynamic-tree-term (car tree))
         (q1259814-dynamic-tree-term (cdr tree)))
      (q1259814-quoted tree))))

(defun q1259814-runtime-quoted-template (runtime-term)
  (list 'quote (q1259814-runtime-node runtime-term)))

;; This template is turned into a tame unary function after a candidate
;; witness has supplied BASIS, REDUCED, EVALUATE, and NORMAL-FORM.

(defun q1259814-free-laws-template
    (carrier multiplication inverse identity)
  (let* ((basis
          (q1259814-runtime-quoted-template
           (q1259814-nth-term 0 'witness)))
         (reduced
          (q1259814-runtime-quoted-template
           (q1259814-nth-term 1 'witness)))
         (evaluate
          (q1259814-runtime-quoted-template
           (q1259814-nth-term 2 'witness)))
         (normal-form
          (q1259814-runtime-quoted-template
           (q1259814-nth-term 3 'witness)))
         (carrier-term
          (q1259814-runtime-quoted-template
           (q1259814-quoted carrier)))
         (multiplication-term
          (q1259814-runtime-quoted-template
           (q1259814-quoted multiplication)))
         (inverse-term
          (q1259814-runtime-quoted-template
           (q1259814-quoted inverse)))
         (identity-term
          (q1259814-runtime-quoted-template
           (q1259814-quoted identity)))
         (unary-case
          (q1259814-tuple-of-length-term 'case 1))
         (binary-case
          (q1259814-tuple-of-length-term 'case 2))
         (word (q1259814-nth-term 0 'case))
         (other-word (q1259814-nth-term 1 'case))
         (letter (list 'car word))
         (rest (list 'cdr word))
         (generator (q1259814-nth-term 0 letter))
         (sign (q1259814-nth-term 1 letter))
         (next-letter (list 'car rest))
         (next-generator
          (q1259814-nth-term 0 next-letter))
         (next-sign
          (q1259814-nth-term 1 next-letter))
         (valid-sign
          (q1259814-or-terms
           (list
            (list 'equal sign (q1259814-quoted t))
            (list 'equal sign (q1259814-quoted nil)))))
         (valid-letter
          (q1259814-and-terms
           (list
            (q1259814-tuple-of-length-term letter 2)
            valid-sign
            (q1259814-member-term basis generator))))
         (adjacent-inverses
          (q1259814-and-terms
           (list
            (list 'equal generator next-generator)
            (q1259814-not-term
             (list 'equal sign next-sign)))))
         (expected-reduced
          (list
           'if
           (list 'consp word)
           (q1259814-and-terms
            (list
             valid-letter
             (q1259814-member-term reduced rest)
             (q1259814-implies-term
              (list 'consp rest)
              (q1259814-not-term adjacent-inverses))))
           (list 'equal word (q1259814-quoted nil))))
         (letter-value
          (list
           'if
           (list 'equal sign (q1259814-quoted t))
           generator
           (q1259814-inv-term inverse-term generator)))
         (expected-value
          (list
           'if
           (list 'consp word)
           (q1259814-mul-term
            multiplication-term
            letter-value
            (q1259814-apply-term evaluate (list rest)))
           identity-term))
         (word-value
          (q1259814-apply-term evaluate (list word)))
         (other-word-value
          (q1259814-apply-term evaluate (list other-word)))
         (normal-word
          (q1259814-apply-term normal-form (list word))))
    (list
     'lambda
     '(case)
     (q1259814-and-terms
      (list
       (q1259814-implies-term
        unary-case
        (q1259814-and-terms
         (list
          (q1259814-implies-term
           (q1259814-member-term basis word)
           (q1259814-member-term carrier-term word))
          (q1259814-iff-term
           (q1259814-member-term reduced word)
           expected-reduced)
          (list 'equal word-value expected-value)
          (q1259814-implies-term
           (q1259814-member-term carrier-term word)
           (q1259814-and-terms
            (list
             (q1259814-member-term reduced normal-word)
             (list
              'equal
              (q1259814-apply-term
               evaluate
               (list normal-word))
              word))))
          (q1259814-implies-term
           (q1259814-member-term reduced word)
           (q1259814-member-term carrier-term word-value)))))
       (q1259814-implies-term
        (q1259814-and-terms
         (list
          binary-case
          (q1259814-member-term reduced word)
          (q1259814-member-term reduced other-word)
          (list 'equal word-value other-word-value)))
        (list 'equal word other-word)))))))

(defun q1259814-free-witness-condition-function
    (carrier multiplication inverse identity)
  (let* ((laws-template
          (q1259814-free-laws-template
           carrier multiplication inverse identity))
         (laws
          (q1259814-dynamic-tree-term laws-template))
         (always-true
          (q1259814-true-function '(case))))
    (list
     'lambda
     '(witness)
     (q1259814-and-terms
      (list
       (q1259814-tuple-of-length-term 'witness 4)
       (list
        'tamep-functionp
        (q1259814-nth-term 0 'witness))
       (list
        'tamep-functionp
        (q1259814-nth-term 1 'witness))
       (list
        'tamep-functionp
        (q1259814-nth-term 2 'witness))
       (list
        'tamep-functionp
        (q1259814-nth-term 3 'witness))
       (list 'tamep-functionp laws)
       (list
        'fn-equal
        laws
        (q1259814-quoted always-true)))))))

(defun q1259814-free-group-p
    (carrier multiplication inverse identity)
  (and
   (q1259814-group-p
    carrier multiplication inverse identity)
   (q1259814-exists-p
    (q1259814-free-witness-condition-function
     carrier multiplication inverse identity)
    '(witness))))

(defun thousand-theorems-q1259814-subgroup-is-free-of-is-free-statement
    (carrier multiplication inverse identity subgroup)
  (implies
   (and
    (q1259814-subgroup-p
     carrier multiplication inverse identity subgroup)
    (q1259814-free-group-p
     carrier multiplication inverse identity))
   (q1259814-free-group-p
    subgroup multiplication inverse identity)))

(value-triple :itpeval-statement-checked)
:q
