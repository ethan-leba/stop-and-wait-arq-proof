; ****************** BEGIN INITIALIZATION FOR ACL2s MODE ****************** ;
; (Nothing to see here!  Your actual file is after this initialization code);
 (make-event
 (er-progn
  (set-deferred-ttag-notes t state)
  (value '(value-triple :invisible))))

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading the CCG book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/ccg/ccg" :uncertified-okp nil :dir :system :ttags ((:ccg)) :load-compiled-file nil);v4.0 change

;Common base theory for all modes.
#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s base theory book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/base-theory" :dir :system :ttags :all)


#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/custom" :dir :system :ttags :all)

;; guard-checking-on is in *protected-system-state-globals* so any
;; changes are reverted back to what they were if you try setting this
;; with make-event. So, in order to avoid the use of progn! and trust
;; tags (which would not have been a big deal) in custom.lisp, I
;; decided to add this here.
;; 
;; How to check (f-get-global 'guard-checking-on state)
;; (acl2::set-guard-checking :nowarn)
(acl2::set-guard-checking :all)

;Settings common to all ACL2s modes
(acl2s-common-settings)
;(acl2::xdoc acl2s::defunc) ;; 3 seconds is too much time to spare -- commenting out [2015-02-01 Sun]

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/acl2s-sigs" :dir :system :ttags :all)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem setting up ACL2s mode.") (value :invisible))

(acl2::xdoc acl2s::defunc) ; almost 3 seconds

; Non-events:
;(set-guard-checking :none)

(set-inhibit-warnings! "Invariant-risk" "theory")

(in-package "ACL2")
(redef+)
(defun print-ttag-note (val active-book-name include-bookp deferred-p state)
  (declare (xargs :stobjs state)
	   (ignore val active-book-name include-bookp deferred-p))
  state)

(defun print-deferred-ttag-notes-summary (state)
  (declare (xargs :stobjs state))
  state)

(defun notify-on-defttag (val active-book-name include-bookp state)
  (declare (xargs :stobjs state)
	   (ignore val active-book-name include-bookp))
  state)
(redef-)

(acl2::in-package "ACL2S")

; ******************* END INITIALIZATION FOR ACL2s MODE ******************* ;
;$ACL2s-SMode$;ACL2s

;; ---- Definitions ----

(defdata data (listof atom))

(defdata sender-state data)

(defdata receiver-state data)

(defdata sim-state (list sender-state receiver-state))

;; LHS contains the sender's updated state, RHS is the packet to be sent
(defdata sender-out (cons sender-state atom))

;; ---- Functions ----

(definec sender (sender-state :sender-state) :sender-out
  (cons (cdr sender-state) (car sender-state)))

(definec receiver (receiver-state :receiver-state packet :atom) :receiver-state
  (app receiver-state (list packet)))

(definec simulator-step (sim :sim-state) :sim-state
  (let* ((ss (first sim))
	 (rs (second sim))
	 (ss-out (sender ss))
	 (new-ss (car ss-out))
	 (packet (cdr ss-out))
	 (new-rs (receiver rs packet)))
    (list new-ss new-rs)))

(definec simulator (ss :sender-state rs :receiver-state) :data
  (cond
   ((lendp ss) rs)
   (T (let* ((ss-out (sender ss))
	     (new-ss (car ss-out))
	     (packet (cdr ss-out))
	     (new-rs (receiver rs packet)))
	(simulator new-ss new-rs)))))

;; ---- Proofs ----

(definec simulator* (data :data) :data
  (simulator data '()))

(definec f (data :data) :data
  (if (lendp data)
      data
    (cons (car data) (f (cdr data)))))

(defthm f-identity
  (implies (and (datap l))
	   (equal (f l) l)))

(defthm f-sim-relation
  (implies (and (datap in)
		(datap out))
	   (equal (simulator in out) (app out (f in))))
  :hints (("Goal" :induct (simulator in out))))

(defthm sim*-equiv-f
  (implies (and (datap d))
	   (equal (simulator* d) (f d))))

(defthm simulator-is-correct
  (implies (and (datap data))
	   (equal (simulator* data) data)))

