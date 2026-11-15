;; Statement-only formalization of VERINA corpus artifact verina_basic_104,
;; catalog title "update_map": a deterministic integer-map program lets the
;; second map override the first and sorts the resulting entries by key, with
;; its complete lookup and no-extra-entry contract. This file contains no proof.

(in-package "ACL2")

;; The source Map Int Int structure is represented by its entries field: a
;; proper list of dotted integer pairs (key . value).

(defun verina-basic-104-integer-map-p (entries)
  (declare (xargs :measure (acl2-count entries)))
  (if (consp entries)
      (let ((entry (car entries)))
        (and
         (consp entry)
         (integerp (car entry))
         (integerp (cdr entry))
         (verina-basic-104-integer-map-p
          (cdr entries))))
    (equal entries nil)))

;; These definitions express List.Nodup after mapping Prod.fst.

(defun verina-basic-104-key-member-p (key entries)
  (declare (xargs :measure (acl2-count entries)))
  (if (consp entries)
      (or
       (equal key (car (car entries)))
       (verina-basic-104-key-member-p
        key
        (cdr entries)))
    nil))

(defun verina-basic-104-unique-keys-p (entries)
  (declare (xargs :measure (acl2-count entries)))
  (if (consp entries)
      (and
       (not
        (verina-basic-104-key-member-p
         (car (car entries))
         (cdr entries)))
       (verina-basic-104-unique-keys-p
        (cdr entries)))
    (equal entries nil)))

(defun verina-basic-104-update-map-precond (m1 m2)
  (and
   (verina-basic-104-unique-keys-p m1)
   (verina-basic-104-unique-keys-p m2)))

;; INSERT first filters every entry whose key equals KEY, preserving the order
;; of all other entries, and then appends (KEY . VALUE). This is the source
;; filter followed by singleton append.

(defun verina-basic-104-remove-key (key entries)
  (declare (xargs :measure (acl2-count entries)))
  (if (consp entries)
      (if (equal key (car (car entries)))
          (verina-basic-104-remove-key
           key
           (cdr entries))
        (cons
         (car entries)
         (verina-basic-104-remove-key
          key
          (cdr entries))))
    nil))

(defun verina-basic-104-insert
    (entries key value)
  (append
   (verina-basic-104-remove-key key entries)
   (list (cons key value))))

;; This tail recursion is m2.entries.foldl foldFn m1.

(defun verina-basic-104-fold-inserts
    (remaining accumulator)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (let ((entry (car remaining)))
        (verina-basic-104-fold-inserts
         (cdr remaining)
         (verina-basic-104-insert
          accumulator
          (car entry)
          (cdr entry))))
    accumulator))

;; Under the source precondition, folding INSERT produces unique keys.
;; Insertion sorting by key is therefore extensionally identical to
;; List.mergeSort (fun a b => a.1 <= b.1): each returns the unique ascending
;; ordering of exactly the same entries.

(defun verina-basic-104-insert-sorted-entry
    (entry sorted)
  (declare (xargs :measure (acl2-count sorted)))
  (if (consp sorted)
      (if (<= (car entry)
              (car (car sorted)))
          (cons entry sorted)
        (cons
         (car sorted)
         (verina-basic-104-insert-sorted-entry
          entry
          (cdr sorted))))
    (list entry)))

(defun verina-basic-104-sort-entries (entries)
  (declare (xargs :measure (acl2-count entries)))
  (if (consp entries)
      (verina-basic-104-insert-sorted-entry
       (car entries)
       (verina-basic-104-sort-entries
        (cdr entries)))
    nil))

;; The proof-valued precondition argument is computationally irrelevant and is
;; erased. All executable data transformations remain connected exactly as in
;; the source update_map definition.

(defun verina-basic-104-update-map (m1 m2)
  (verina-basic-104-sort-entries
   (verina-basic-104-fold-inserts
    m2
    m1)))

;; Tagged dotted pairs (:some . value) and the atom :none represent Option Int
;; without identifying none with any possible integer value. The scan returns
;; the first matching entry, exactly as List.find? followed by Option.map snd.

(defun verina-basic-104-find-option
    (entries key)
  (declare (xargs :measure (acl2-count entries)))
  (if (consp entries)
      (let ((entry (car entries)))
        (if (equal (car entry) key)
            (cons :some (cdr entry))
          (verina-basic-104-find-option
           (cdr entries)
           key)))
    :none))

(defun verina-basic-104-some-option-p (option)
  (and
   (consp option)
   (equal (car option) :some)
   (integerp (cdr option))))

(defun verina-basic-104-option-value (option)
  (cdr option))

;; List.Pairwise requires each head key to be at most every later key, and
;; recursively imposes the same requirement on the tail.

(defun verina-basic-104-key-at-most-all-p
    (key entries)
  (declare (xargs :measure (acl2-count entries)))
  (if (consp entries)
      (and
       (<= key (car (car entries)))
       (verina-basic-104-key-at-most-all-p
        key
        (cdr entries)))
    (equal entries nil)))

(defun verina-basic-104-pairwise-key-order-p
    (entries)
  (declare (xargs :measure (acl2-count entries)))
  (if (consp entries)
      (and
       (verina-basic-104-key-at-most-all-p
        (car (car entries))
        (cdr entries))
       (verina-basic-104-pairwise-key-order-p
        (cdr entries)))
    (equal entries nil)))

;; Every m2 entry must be found in RESULT with its original value.

(defun verina-basic-104-all-m2-entries-present-p
    (remaining result)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (let ((entry (car remaining)))
        (and
         (equal
          (verina-basic-104-find-option
           result
           (car entry))
          (cons :some (cdr entry)))
         (verina-basic-104-all-m2-entries-present-p
          (cdr remaining)
          result)))
    (equal remaining nil)))

;; For each m1 entry, a key present in m2 imposes no additional clause here;
;; otherwise RESULT must retain the m1 value.

(defun verina-basic-104-all-unoverridden-m1-entries-present-p
    (remaining m2 result)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (let* ((entry (car remaining))
             (from-m2
              (verina-basic-104-find-option
               m2
               (car entry))))
        (and
         (if (verina-basic-104-some-option-p from-m2)
             t
           (equal
            (verina-basic-104-find-option
             result
             (car entry))
            (cons :some (cdr entry))))
         (verina-basic-104-all-unoverridden-m1-entries-present-p
          (cdr remaining)
          m2
          result)))
    (equal remaining nil)))

;; Every result entry must carry m2's value when its key occurs there, m1's
;; value when it occurs only in m1, and otherwise be witnessed by m2. This is
;; the source's final List.all match expression and excludes extra entries.

(defun verina-basic-104-all-result-entries-valid-p
    (remaining m1 m2)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (let* ((entry (car remaining))
             (key (car entry))
             (value (cdr entry))
             (from-m1
              (verina-basic-104-find-option m1 key))
             (from-m2
              (verina-basic-104-find-option m2 key)))
        (and
         (if (verina-basic-104-some-option-p from-m1)
             (if (verina-basic-104-some-option-p from-m2)
                 (equal
                  value
                  (verina-basic-104-option-value
                   from-m2))
               (equal
                value
                (verina-basic-104-option-value
                 from-m1)))
           (equal
            from-m2
            (cons :some value)))
         (verina-basic-104-all-result-entries-valid-p
          (cdr remaining)
          m1
          m2)))
    (equal remaining nil)))

(defun verina-basic-104-update-map-postcond
    (m1 m2 result)
  (and
   (verina-basic-104-integer-map-p m1)
   (verina-basic-104-integer-map-p m2)
   (verina-basic-104-integer-map-p result)
   (verina-basic-104-pairwise-key-order-p result)
   (verina-basic-104-all-m2-entries-present-p
    m2
    result)
   (verina-basic-104-all-unoverridden-m1-entries-present-p
    m1
    m2
    result)
   (verina-basic-104-all-result-entries-valid-p
    result
    m1
    m2)))

;; This predicate is the unproved final correctness proposition. Its
;; antecedent preserves both arbitrary Map Int Int inputs and the complete
;; unique-key precondition; its conclusion applies the full postcondition to
;; the exact executable update_map result.

(defun verina-basic-104-update-map-spec-satisfied-statement
    (m1 m2)
  (implies
   (and
    (verina-basic-104-integer-map-p m1)
    (verina-basic-104-integer-map-p m2)
    (verina-basic-104-update-map-precond
     m1
     m2))
   (verina-basic-104-update-map-postcond
    m1
    m2
    (verina-basic-104-update-map m1 m2))))

(value-triple :itpeval-statement-checked)
:q
