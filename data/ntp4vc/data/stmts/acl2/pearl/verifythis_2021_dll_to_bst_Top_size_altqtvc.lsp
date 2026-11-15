;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/verifythis_2021_dll_to_bst_Top_size_altqtvc: the iterative traversal
;; of a well-formed doubly linked list, preserving its segment invariant while
;; advancing one node and decreasing the remaining-length variant.
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
;; duplicate-key entries. Entry order is immaterial.

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
       (equal key (dbst-fmap-entry-key (car map)))
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
      (if (equal key (dbst-fmap-entry-key (car map)))
          (dbst-fmap-entry-value (car map))
        (dbst-fmap-lookup key (cdr map)))
    (dbst-default-loc)))

(defun-sk dbst-to-fmap-typed-p ()
  (forall (map-value)
    (implies
     (dbst-map-value-p map-value)
     (dbst-fmap-p (dbst-to-fmap map-value)))))

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
         (not (equal location (dbst-null)))
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

;; This is the loop continuation generated from the source invariant and
;; variant. The map-membership guard precedes the exact one-step NEXT lookup.

(defun dbst-size-alt-continuation-p
    (prev next sequence length-index location)
  (implies
   (dbst-dll-p
    prev
    next
    sequence
    location
    length-index
    (len sequence))
   (if (not (equal location (dbst-null)))
       (and
        (dbst-fmap-member-p location next)
        (let ((next-location
               (dbst-fmap-lookup location next)))
          (implies
           (equal
            next-location
            (dbst-fmap-lookup location next))
           (and
            (<= 0 (- (len sequence) length-index))
            (<
             (- (len sequence) (+ length-index 1))
             (- (len sequence) length-index))
            (dbst-dll-p
             prev
             next
             sequence
             next-location
             (+ length-index 1)
             (len sequence))))))
     (equal length-index (len sequence)))))

(defun-sk dbst-all-size-alt-continuations-p
    (prev next sequence)
  (forall (length-index location)
    (implies
     (and
      (integerp length-index)
      (dbst-loc-p location))
     (dbst-size-alt-continuation-p
      prev next sequence length-index location))))

;; FACT0 is the sole source precondition. The conclusion repeats FACT0 and
;; universally preserves the loop invariant, variant bounds, and exit case.

(defun-sk
    ntp4vc-pearl-verifythis-2021-dll-to-bst-top-size-altqtvc-statement
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
      (dbst-all-size-alt-continuations-p
       (dbst-to-fmap prev)
       (dbst-to-fmap next)
       sequence)))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
