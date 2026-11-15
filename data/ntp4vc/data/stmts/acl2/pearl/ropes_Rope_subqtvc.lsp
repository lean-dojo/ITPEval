;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/ropes_Rope_subqtvc: the rope substring verification condition,
;; preserving recursive branch bounds, rope invariants, and extensional
;; agreement with the modeled string substring. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-gag-mode t)

;; The source character and immutable-string types are arbitrary inhabited
;; carriers. These conservative interfaces provide the operations from the
;; imported MyString theory; every typing and mathematical law is an explicit
;; premise of the statement.

(defstub rrs-char-p (value) t)
(defstub rrs-char-string-p (value) t)
(defstub rrs-dummy-char () t)
(defstub rrs-string-empty () t)
(defstub rrs-string-length (string) t)
(defstub rrs-string-index (string index) t)
(defstub rrs-string-app (left right) t)
(defstub rrs-string-sub (string offset length) t)

(defun-sk rrs-string-function-types-p ()
  (forall (string left right index offset length)
    (and
     (implies
      (rrs-char-string-p string)
      (integerp
       (rrs-string-length string)))
     (implies
      (and
       (rrs-char-string-p string)
       (integerp index))
      (rrs-char-p
       (rrs-string-index string index)))
     (implies
      (and
       (rrs-char-string-p left)
       (rrs-char-string-p right))
      (rrs-char-string-p
       (rrs-string-app left right)))
     (implies
      (and
       (rrs-char-string-p string)
       (integerp offset)
       (integerp length))
      (rrs-char-string-p
       (rrs-string-sub
        string offset length))))))

(defun-sk rrs-string-length-nonnegative-p ()
  (forall (string)
    (implies
     (rrs-char-string-p string)
     (<= 0
         (rrs-string-length string)))))

(defun-sk rrs-strings-agree-p (left right)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index (rrs-string-length left)))
      (equal
       (rrs-string-index left index)
       (rrs-string-index right index))))))

(defun rrs-string-equal-p (left right)
  (and
   (rrs-char-string-p left)
   (rrs-char-string-p right)
   (equal
    (rrs-string-length left)
    (rrs-string-length right))
   (rrs-strings-agree-p left right)))

(defun-sk rrs-string-extensionality-p ()
  (forall (left right)
    (implies
     (and
      (rrs-char-string-p left)
      (rrs-char-string-p right)
      (rrs-string-equal-p left right))
     (equal left right))))

(defun-sk rrs-string-app-length-law-p ()
  (forall (left right)
    (implies
     (and
      (rrs-char-string-p left)
      (rrs-char-string-p right))
     (equal
      (rrs-string-length
       (rrs-string-app left right))
      (+ (rrs-string-length left)
         (rrs-string-length right))))))

(defun-sk rrs-string-app-left-law-p ()
  (forall (left right index)
    (implies
     (and
      (rrs-char-string-p left)
      (rrs-char-string-p right)
      (integerp index)
      (<= 0 index)
      (< index
         (rrs-string-length left)))
     (equal
      (rrs-string-index
       (rrs-string-app left right)
       index)
      (rrs-string-index left index)))))

(defun-sk rrs-string-app-right-law-p ()
  (forall (left right index)
    (implies
     (and
      (rrs-char-string-p left)
      (rrs-char-string-p right)
      (integerp index)
      (<= (rrs-string-length left)
          index)
      (< index
         (+ (rrs-string-length left)
            (rrs-string-length right))))
     (equal
      (rrs-string-index
       (rrs-string-app left right)
       index)
      (rrs-string-index
       right
       (- index
          (rrs-string-length left)))))))

(defun-sk rrs-string-sub-length-law-p ()
  (forall (string offset length)
    (implies
     (and
      (rrs-char-string-p string)
      (integerp offset)
      (integerp length)
      (<= 0 length)
      (<= 0 offset)
      (<= offset
          (rrs-string-length string))
      (<= (+ offset length)
          (rrs-string-length string)))
     (equal
      (rrs-string-length
       (rrs-string-sub
        string offset length))
      length))))

(defun-sk rrs-string-sub-index-law-p ()
  (forall (string offset length index)
    (implies
     (and
      (rrs-char-string-p string)
      (integerp offset)
      (integerp length)
      (integerp index)
      (<= 0 length)
      (<= 0 offset)
      (<= offset
          (rrs-string-length string))
      (<= (+ offset length)
          (rrs-string-length string))
      (<= 0 index)
      (< index length))
     (equal
      (rrs-string-index
       (rrs-string-sub
        string offset length)
       index)
      (rrs-string-index
       string
       (+ offset index))))))

(defun rrs-mystring-background-p ()
  (and
   (rrs-char-p
    (rrs-dummy-char))
   (rrs-char-string-p
    (rrs-string-empty))
   (equal
    (rrs-string-length
     (rrs-string-empty))
    0)
   (rrs-string-function-types-p)
   (rrs-string-length-nonnegative-p)
   (rrs-string-extensionality-p)
   (rrs-string-app-length-law-p)
   (rrs-string-app-left-law-p)
   (rrs-string-app-right-law-p)
   (rrs-string-sub-length-law-p)
   (rrs-string-sub-index-law-p)))

;; These tagged records are an exact encoding of the finite inductive datatype
;; Emp | Str char_string int int | App rope rope int.

(defun rrs-emp ()
  (list :rrs-emp))

(defun rrs-str (string offset length)
  (list :rrs-str string offset length))

(defun rrs-app (left right length)
  (list :rrs-app left right length))

(defun rrs-emp-p (rope)
  (equal rope (rrs-emp)))

(defun rrs-str-shape-p (rope)
  (and
   (true-listp rope)
   (equal (len rope) 4)
   (equal (car rope) :rrs-str)))

(defun rrs-app-shape-p (rope)
  (and
   (true-listp rope)
   (equal (len rope) 4)
   (equal (car rope) :rrs-app)))

(defun rrs-str-string (rope)
  (cadr rope))

(defun rrs-str-offset (rope)
  (caddr rope))

(defun rrs-str-length (rope)
  (cadddr rope))

(defun rrs-app-left (rope)
  (cadr rope))

(defun rrs-app-right (rope)
  (caddr rope))

(defun rrs-app-length (rope)
  (cadddr rope))

(defun rrs-rope-p (rope)
  (declare (xargs :measure (acl2-count rope)))
  (cond
   ((rrs-emp-p rope)
    t)
   ((rrs-str-shape-p rope)
    (and
     (rrs-char-string-p
      (rrs-str-string rope))
     (integerp
      (rrs-str-offset rope))
     (integerp
      (rrs-str-length rope))))
   ((rrs-app-shape-p rope)
    (and
     (rrs-rope-p
      (rrs-app-left rope))
     (rrs-rope-p
      (rrs-app-right rope))
     (integerp
      (rrs-app-length rope))))
   (t nil)))

(defun rrs-rope-length (rope)
  (cond
   ((rrs-emp-p rope)
    0)
   ((rrs-str-shape-p rope)
    (rrs-str-length rope))
   ((rrs-app-shape-p rope)
    (rrs-app-length rope))
   (t 0)))

(defun rrs-rope-inv-p (rope)
  (declare (xargs :measure (acl2-count rope)))
  (cond
   ((rrs-emp-p rope)
    t)
   ((rrs-str-shape-p rope)
    (let ((string
           (rrs-str-string rope))
          (offset
           (rrs-str-offset rope))
          (length
           (rrs-str-length rope)))
      (and
       (< 0 length)
       (<= 0 offset)
       (< offset
          (rrs-string-length string))
       (<= (+ offset length)
           (rrs-string-length string)))))
   ((rrs-app-shape-p rope)
    (let ((left
           (rrs-app-left rope))
          (right
           (rrs-app-right rope))
          (stored-length
           (rrs-app-length rope)))
      (and
       (< 0
          (rrs-rope-length left))
       (rrs-rope-inv-p left)
       (< 0
          (rrs-rope-length right))
       (rrs-rope-inv-p right)
       (equal
        stored-length
        (+ (rrs-rope-length left)
           (rrs-rope-length right))))))
   (t nil)))

(defun rrs-rope-string (rope)
  (declare (xargs :measure (acl2-count rope)))
  (cond
   ((rrs-emp-p rope)
    (rrs-string-empty))
   ((rrs-str-shape-p rope)
    (rrs-string-sub
     (rrs-str-string rope)
     (rrs-str-offset rope)
     (rrs-str-length rope)))
   ((rrs-app-shape-p rope)
    (rrs-string-app
     (rrs-rope-string
      (rrs-app-left rope))
     (rrs-rope-string
      (rrs-app-right rope))))
   (t
    (rrs-string-empty))))

;; This is the repeated match on the original App value in the exported VC.

(defun rrs-app-child-p (source child)
  (and
   (rrs-app-shape-p source)
   (or
    (equal
     (rrs-app-left source)
     child)
    (equal
     (rrs-app-right source)
     child))))

;; In the split branch, O2 remains universally quantified inside the
;; implication for a fixed possible O1 returned by the right recursive call.

(defun-sk rrs-split-left-result-universal-p
    (source left offset left-length right-result)
  (forall (left-result)
    (implies
     (rrs-rope-p left-result)
     (implies
      (and
       (rrs-rope-inv-p left-result)
       (rrs-string-equal-p
        (rrs-rope-string left-result)
        (rrs-string-sub
         (rrs-rope-string left)
         offset
         left-length)))
      (and
       (rrs-rope-inv-p left-result)
       (rrs-rope-inv-p right-result))))))

;; O1 remains universally quantified over all ropes satisfying the right
;; recursive call's postcondition.

(defun-sk rrs-split-right-result-universal-p
    (source left right offset left-length right-length)
  (forall (right-result)
    (implies
     (rrs-rope-p right-result)
     (implies
      (and
       (rrs-rope-inv-p right-result)
       (rrs-string-equal-p
        (rrs-rope-string right-result)
        (rrs-string-sub
         (rrs-rope-string right)
         0
         right-length)))
      (and
       (rrs-app-child-p source left)
       (rrs-rope-inv-p left)
       (<= 0 left-length)
       (<= 0 offset)
       (<= offset
           (rrs-rope-length left))
       (<= (+ offset left-length)
           (rrs-rope-length left))
       (rrs-split-left-result-universal-p
        source
        left
        offset
        left-length
        right-result))))))

;; This preserves the first match expression in the VC, including the exact
;; recursive-call bounds in all three App subcases.

(defun rrs-recursive-call-obligations-p
    (source length offset)
  (cond
   ((rrs-emp-p source)
    t)
   ((rrs-str-shape-p source)
    t)
   ((rrs-app-shape-p source)
    (let* ((left
            (rrs-app-left source))
           (right
            (rrs-app-right source))
           (left-length
            (- (rrs-rope-length left)
               offset))
           (right-length
            (- length left-length)))
      (if (<= right-length 0)
          (and
           (rrs-app-child-p source left)
           (rrs-rope-inv-p left)
           (<= 0 length)
           (<= 0 offset)
           (<= offset
               (rrs-rope-length left))
           (<= (+ offset length)
               (rrs-rope-length left)))
        (if (<= left-length 0)
            (let ((right-offset
                   (- left-length)))
              (and
               (rrs-app-child-p source right)
               (rrs-rope-inv-p right)
               (<= 0 length)
               (<= 0 right-offset)
               (<= right-offset
                   (rrs-rope-length right))
               (<= (+ right-offset length)
                   (rrs-rope-length right))))
          (and
           (rrs-app-child-p source right)
           (rrs-rope-inv-p right)
           (<= 0 right-length)
           (<= 0 0)
           (<= 0
               (rrs-rope-length right))
           (<= (+ 0 right-length)
               (rrs-rope-length right))
           (rrs-split-right-result-universal-p
            source
            left
            right
            offset
            left-length
            right-length))))))
   (t nil)))

;; These two existential predicates retain the possible recursive results O1
;; and O2 inside the App split branch's result premise.

(defun-sk rrs-split-left-result-exists-p
    (left right offset left-length right-result result)
  (exists (left-result)
    (and
     (rrs-rope-p left-result)
     (rrs-rope-inv-p left-result)
     (rrs-string-equal-p
      (rrs-rope-string left-result)
      (rrs-string-sub
       (rrs-rope-string left)
       offset
       left-length))
     (rrs-rope-inv-p result)
     (rrs-string-equal-p
      (rrs-rope-string result)
      (rrs-string-app
       (rrs-rope-string left-result)
       (rrs-rope-string right-result))))))

(defun-sk rrs-split-right-result-exists-p
    (left right offset left-length right-length result)
  (exists (right-result)
    (and
     (rrs-rope-p right-result)
     (rrs-rope-inv-p right-result)
     (rrs-string-equal-p
      (rrs-rope-string right-result)
      (rrs-string-sub
       (rrs-rope-string right)
       0
       right-length))
     (rrs-split-left-result-exists-p
      left
      right
      offset
      left-length
      right-result
      result))))

;; This is the second source match: it characterizes every possible result of
;; the recursive substring computation in the corresponding branch.

(defun rrs-result-premise-p
    (source length offset result)
  (cond
   ((rrs-emp-p source)
    (equal result
           (rrs-emp)))
   ((rrs-str-shape-p source)
    (if (equal length 0)
        (equal result
               (rrs-emp))
      (equal
       result
       (rrs-str
        (rrs-str-string source)
        (+ (rrs-str-offset source)
           offset)
        length))))
   ((rrs-app-shape-p source)
    (let* ((left
            (rrs-app-left source))
           (right
            (rrs-app-right source))
           (left-length
            (- (rrs-rope-length left)
               offset))
           (right-length
            (- length left-length)))
      (if (<= right-length 0)
          (and
           (rrs-rope-inv-p result)
           (rrs-string-equal-p
            (rrs-rope-string result)
            (rrs-string-sub
             (rrs-rope-string left)
             offset
             length)))
        (if (<= left-length 0)
            (and
             (rrs-rope-inv-p result)
             (rrs-string-equal-p
              (rrs-rope-string result)
              (rrs-string-sub
               (rrs-rope-string right)
               (- left-length)
               length)))
          (rrs-split-right-result-exists-p
           left
           right
           offset
           left-length
           right-length
           result)))))
   (t nil)))

;; RESULT stays universally quantified over the full rope datatype, and the
;; conclusion is the complete invariant-and-modeled-substring postcondition.

(defun-sk rrs-all-results-p
    (source length offset)
  (forall (result)
    (implies
     (rrs-rope-p result)
     (implies
      (rrs-result-premise-p
       source length offset result)
      (and
       (rrs-rope-inv-p result)
       (rrs-string-equal-p
        (rrs-rope-string result)
        (rrs-string-sub
         (rrs-rope-string source)
         offset
         length)))))))

(defun-sk
    ntp4vc-pearl-ropes-rope-subqtvc-statement ()
  (forall (source length offset)
    (implies
     (and
      (rrs-mystring-background-p)
      (rrs-rope-p source)
      (integerp length)
      (integerp offset)
      (rrs-rope-inv-p source)
      (<= 0 length)
      (<= 0 offset)
      (<= offset
          (rrs-rope-length source))
      (<= (+ offset length)
          (rrs-rope-length source)))
     (and
      (rrs-recursive-call-obligations-p
       source length offset)
      (rrs-all-results-p
       source length offset)))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
