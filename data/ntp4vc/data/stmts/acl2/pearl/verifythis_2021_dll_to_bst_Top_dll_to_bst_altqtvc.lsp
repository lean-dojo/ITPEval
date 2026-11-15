;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/verifythis_2021_dll_to_bst_Top_dll_to_bst_altqtvc: the alternate
;; doubly-linked-list to balanced binary-search-tree verification condition,
;; preserving map domains, inorder locations, tree size, and height bounds.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-gag-mode t)

;; Locations and imperative-map values retain their arbitrary inhabited source
;; domains. TO-FMAP is the conservative interface to the source finite map.

(defstub dbst-loc-p (location) t)
(defstub dbst-null () t)
(defstub dbst-default-loc () t)
(defstub dbst-map-value-p (map-value) t)
(defstub dbst-to-fmap (map-value) t)

(defun-sk dbst-loc-domain-nonempty-p ()
  (exists (location)
    (dbst-loc-p location)))

(defun-sk dbst-map-value-domain-nonempty-p ()
  (exists (map-value)
    (dbst-map-value-p map-value)))

;; A finite loc-to-loc map is represented exactly by a finite list of tagged,
;; duplicate-key entries. Entry order is immaterial; domain equality below is
;; extensional.

(defun dbst-fmap-entry-p (entry)
  (and
   (true-listp entry)
   (equal (len entry) 3)
   (equal (car entry) :dbst-entry)
   (dbst-loc-p (cadr entry))
   (dbst-loc-p (caddr entry))))

(defun dbst-fmap-entry-key (entry)
  (cadr entry))

(defun dbst-fmap-entry-value (entry)
  (caddr entry))

(defun dbst-fmap-member-p (key map)
  (declare (xargs :measure (acl2-count map)))
  (if (consp map)
      (or
       (equal key
              (dbst-fmap-entry-key (car map)))
       (dbst-fmap-member-p key (cdr map)))
    nil))

(defun dbst-fmap-p (map)
  (declare (xargs :measure (acl2-count map)))
  (if (consp map)
      (and
       (dbst-fmap-entry-p (car map))
       (not
        (dbst-fmap-member-p
         (dbst-fmap-entry-key (car map))
         (cdr map)))
       (dbst-fmap-p (cdr map)))
    (equal map nil)))

(defun dbst-fmap-lookup (key map)
  (declare (xargs :measure (acl2-count map)))
  (if (consp map)
      (if (equal
           key
           (dbst-fmap-entry-key (car map)))
          (dbst-fmap-entry-value (car map))
        (dbst-fmap-lookup key (cdr map)))
    (dbst-default-loc)))

(defun dbst-fmap-domain-subset-p (left right)
  (declare (xargs :measure (acl2-count left)))
  (if (consp left)
      (and
       (dbst-fmap-member-p
        (dbst-fmap-entry-key (car left))
        right)
       (dbst-fmap-domain-subset-p
        (cdr left)
        right))
    (equal left nil)))

(defun dbst-fmap-domain-equal-p (left right)
  (and
   (dbst-fmap-domain-subset-p left right)
   (dbst-fmap-domain-subset-p right left)))

(defun-sk dbst-to-fmap-typed-p ()
  (forall (map-value)
    (implies
     (dbst-map-value-p map-value)
     (dbst-fmap-p
      (dbst-to-fmap map-value)))))

(defun dbst-interface-p ()
  (and
   (dbst-loc-domain-nonempty-p)
   (dbst-map-value-domain-nonempty-p)
   (dbst-loc-p (dbst-null))
   (dbst-loc-p (dbst-default-loc))
   (dbst-to-fmap-typed-p)))

;; Why3 sequences of locations are represented bijectively by proper finite
;; ACL2 lists of locations.

(defun dbst-loc-list-p (sequence)
  (declare (xargs :measure (acl2-count sequence)))
  (if (consp sequence)
      (and
       (dbst-loc-p (car sequence))
       (dbst-loc-list-p (cdr sequence)))
    (equal sequence nil)))

(defun dbst-int-to-nat (value)
  (if (and
       (integerp value)
       (< value 0))
      0
    (nfix value)))

(defun dbst-sequence-get (sequence index)
  (let ((tail
         (nthcdr
          (dbst-int-to-nat index)
          sequence)))
    (if (consp tail)
        (car tail)
      (dbst-default-loc))))

;; VALID states that every sequence location is non-null, belongs to both map
;; domains, and is distinct from every later sequence location.

(defun-sk dbst-valid-locations-p (prev next sequence)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index (len sequence)))
      (let ((location
             (dbst-sequence-get sequence index)))
        (and
         (not
          (equal location (dbst-null)))
         (dbst-fmap-member-p location prev)
         (dbst-fmap-member-p location next)))))))

(defun-sk dbst-valid-distinct-p (sequence)
  (forall (left-index right-index)
    (implies
     (and
      (integerp left-index)
      (integerp right-index))
     (implies
      (and
       (<= 0 left-index)
       (< left-index right-index)
       (< right-index (len sequence)))
      (not
       (equal
        (dbst-sequence-get sequence left-index)
        (dbst-sequence-get sequence right-index)))))))

(defun dbst-valid-p (prev next sequence)
  (and
   (dbst-fmap-p prev)
   (dbst-fmap-p next)
   (dbst-loc-list-p sequence)
   (dbst-valid-locations-p prev next sequence)
   (dbst-valid-distinct-p sequence)))

;; These two universal predicates are the forward and backward interior links
;; of the source DLL predicate.

(defun-sk dbst-next-links-p
    (next sequence lower upper)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= lower index)
       (< index (- upper 1)))
      (equal
       (dbst-fmap-lookup
        (dbst-sequence-get sequence index)
        next)
       (dbst-sequence-get sequence (+ index 1)))))))

(defun-sk dbst-prev-links-p
    (prev sequence lower upper)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (< lower index)
       (< index upper))
      (equal
       (dbst-fmap-lookup
        (dbst-sequence-get sequence index)
        prev)
       (dbst-sequence-get sequence (- index 1)))))))

(defun dbst-dll-p
    (prev next sequence head lower upper)
  (and
   (dbst-loc-p head)
   (integerp lower)
   (integerp upper)
   (dbst-valid-p prev next sequence)
   (<= 0 lower)
   (<= lower upper)
   (<= upper (len sequence))
   (equal
    head
    (if (equal lower (len sequence))
        (dbst-null)
      (dbst-sequence-get sequence lower)))
   (dbst-next-links-p
    next sequence lower upper)
   (dbst-prev-links-p
    prev sequence lower upper)
   (implies
    (< lower upper)
    (equal
     (dbst-fmap-lookup
      (dbst-sequence-get sequence (- upper 1))
      next)
     (if (equal upper (len sequence))
         (dbst-null)
       (dbst-sequence-get sequence upper))))
   (implies
    (< lower upper)
    (equal
     (dbst-fmap-lookup
      (dbst-sequence-get sequence lower)
      prev)
     (if (equal lower 0)
         (dbst-null)
       (dbst-sequence-get sequence (- lower 1)))))))

;; Empty trees are NIL. Nodes are exact tagged records
;; (:DBST-NODE left integer-position right).

(defun dbst-node-shape-p (tree)
  (and
   (true-listp tree)
   (equal (len tree) 4)
   (equal (car tree) :dbst-node)))

(defun dbst-tree-left (tree)
  (cadr tree))

(defun dbst-tree-position (tree)
  (caddr tree))

(defun dbst-tree-right (tree)
  (cadddr tree))

(defun dbst-tree-p (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (equal tree nil)
      t
    (and
     (dbst-node-shape-p tree)
     (integerp (dbst-tree-position tree))
     (dbst-tree-p (dbst-tree-left tree))
     (dbst-tree-p (dbst-tree-right tree)))))

(defun dbst-tree-size (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (equal tree nil)
      0
    (if (dbst-node-shape-p tree)
        (+
         1
         (dbst-tree-size
          (dbst-tree-left tree))
         (dbst-tree-size
          (dbst-tree-right tree)))
      0)))

(defun dbst-integer-max (left right)
  (if (<= left right)
      right
    left))

(defun dbst-tree-height (tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (equal tree nil)
      0
    (if (dbst-node-shape-p tree)
        (+
         1
         (dbst-integer-max
          (dbst-tree-height
           (dbst-tree-left tree))
          (dbst-tree-height
           (dbst-tree-right tree))))
      0)))

(defun dbst-inorder (sequence tree)
  (declare (xargs :measure (acl2-count tree)))
  (if (equal tree nil)
      nil
    (if (dbst-node-shape-p tree)
        (append
         (dbst-inorder
          sequence
          (dbst-tree-left tree))
         (cons
          (dbst-sequence-get
           sequence
           (dbst-tree-position tree))
          (dbst-inorder
           sequence
           (dbst-tree-right tree))))
      nil)))

;; This is the recursive TREE predicate from the source specification.

(defun dbst-tree-relation-p
    (prev next sequence root tree lower upper)
  (declare (xargs :measure (acl2-count tree)))
  (and
   (dbst-loc-p root)
   (dbst-tree-p tree)
   (integerp lower)
   (integerp upper)
   (dbst-valid-p prev next sequence)
   (<= 0 lower)
   (<= lower upper)
   (<= upper (len sequence))
   (if (equal tree nil)
       (and
        (equal root (dbst-null))
        (equal lower upper))
     (if (dbst-node-shape-p tree)
         (let* ((left
                 (dbst-tree-left tree))
                (position
                 (dbst-tree-position tree))
                (right
                 (dbst-tree-right tree)))
           (and
            (integerp position)
            (<= lower position)
            (< position upper)
            (equal
             root
             (dbst-sequence-get
              sequence position))
            (dbst-tree-relation-p
             prev
             next
             sequence
             (dbst-fmap-lookup root prev)
             left
             lower
             position)
            (dbst-tree-relation-p
             prev
             next
             sequence
             (dbst-fmap-lookup root next)
             right
             (+ position 1)
             upper)))
       nil))))

(defun dbst-height-bound-p (tree size)
  (let ((height
         (dbst-tree-height tree)))
    (and
     (<=
      (expt 2 (- height 1))
      size)
     (< size
        (expt 2 height)))))

;; The source frame conditions compare map values pointwise on an integer
;; interval. This retains even the two explicitly empty intervals in the VC.

(defun-sk dbst-map-agrees-on-range-p
    (left right sequence lower upper)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= lower index)
       (< index upper))
      (equal
       (dbst-fmap-lookup
        (dbst-sequence-get sequence index)
        left)
       (dbst-fmap-lookup
        (dbst-sequence-get sequence index)
        right))))))

;; This is the universally quantified continuation generated after
;; dll_to_bst_rec. Its antecedent contains exactly the recursive-tree result,
;; map-domain preservation, four frame conditions, and conditional balance
;; bound; its conclusion is the wrapper postcondition.

(defun dbst-candidate-result-p
    (prev next sequence n next1 prev1 root tree)
  (let ((old-prev
         (dbst-to-fmap prev))
        (old-next
         (dbst-to-fmap next))
        (new-prev
         (dbst-to-fmap prev1))
        (new-next
         (dbst-to-fmap next1)))
    (implies
     (and
      (dbst-tree-relation-p
       new-prev new-next sequence root tree 0 (+ 0 n))
      (dbst-fmap-domain-equal-p
       new-prev old-prev)
      (dbst-fmap-domain-equal-p
       new-next old-next)
      (dbst-map-agrees-on-range-p
       new-prev old-prev sequence 0 0)
      (dbst-map-agrees-on-range-p
       new-prev old-prev sequence (+ 0 n) (len sequence))
      (dbst-map-agrees-on-range-p
       new-next old-next sequence 0 0)
      (dbst-map-agrees-on-range-p
       new-next old-next sequence (+ 0 n) (len sequence))
      (implies
       (< 0 n)
       (dbst-height-bound-p tree n)))
     (and
      (dbst-tree-relation-p
       new-prev
       new-next
       sequence
       root
       tree
       0
       (len sequence))
      (equal
       (dbst-tree-size tree)
       (len sequence))
      (equal
       (dbst-inorder sequence tree)
       sequence)
      (implies
       (< 0 (len sequence))
       (dbst-height-bound-p
        tree
        (len sequence)))))))

(defun-sk dbst-all-candidate-results-p
    (prev next sequence n)
  (forall (next1 prev1 root tree)
    (implies
     (and
      (dbst-map-value-p next1)
      (dbst-map-value-p prev1)
      (dbst-loc-p root)
      (dbst-tree-p tree))
     (dbst-candidate-result-p
      prev next sequence n
      next1 prev1 root tree))))

;; This is the complete unproved VC. FACT0 is the sole source precondition.
;; The repeated DLL conjunct and the local n = length(sequence) are preserved
;; verbatim before the universal continuation.

(defun-sk
    ntp4vc-pearl-verifythis-2021-dll-to-bst-top-dll-to-bst-altqtvc-statement
    ()
  (forall (prev next sequence head)
    (implies
     (and
      (dbst-interface-p)
      (dbst-map-value-p prev)
      (dbst-map-value-p next)
      (dbst-loc-list-p sequence)
      (dbst-loc-p head)
      (dbst-dll-p
       (dbst-to-fmap prev)
       (dbst-to-fmap next)
       sequence
       head
       0
       (len sequence)))
     (and
      (dbst-dll-p
       (dbst-to-fmap prev)
       (dbst-to-fmap next)
       sequence
       head
       0
       (len sequence))
      (let ((n (len sequence)))
        (and
         (dbst-dll-p
          (dbst-to-fmap prev)
          (dbst-to-fmap next)
          sequence
          head
          0
          (+ 0 n))
         (dbst-all-candidate-results-p
          prev next sequence n)))))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
