use crate::hash;
use crate::storage::{
    self,
    alloc::{AllocateUsing, Initialize},
    chunk::SyncChunk,
    Allocator, Flush,
};

use core::borrow::Borrow;
use core::hash::Hash;

/// Set stored in the contract storage.
///
/// # Note
///
/// This performs a quadratic probing on the next 2^32 slots
/// following its initial key. So it can store up to 2^32 elements in total.
#[derive(Debug)]
pub struct HashSet<K> {
    /// The storage key to the length of this storage set.
    len: storage::Value<u32>,
    members: SyncChunk<K>,
}

impl<K> Flush for HashSet<K>
where
    K: parity_codec::Encode,
{
    fn flush(&mut self) {
        self.len.flush();
        self.members.flush();
    }
}

impl<K> parity_codec::Encode for HashSet<K> {
    fn encode_to<W: parity_codec::Output>(&self, dest: &mut W) {
        self.len.encode_to(dest);
        self.members.encode_to(dest);
    }
}

impl<K> parity_codec::Decode for HashSet<K> {
    fn decode<I: parity_codec::Input>(input: &mut I) -> Option<Self> {
        let len = storage::Value::decode(input)?;
        let members = SyncChunk::decode(input)?;
        Some(Self { len, members })
    }
}

impl<K> AllocateUsing for HashSet<K> {
    unsafe fn allocate_using<A>(alloc: &mut A) -> Self
    where
        A: Allocator,
    {
        Self {
            len: storage::Value::allocate_using(alloc),
            members: SyncChunk::allocate_using(alloc),
        }
    }
}

impl<K> Initialize for HashSet<K> {
    type Args = ();

    fn initialize(&mut self, _args: Self::Args) {
        self.len.set(0);
    }
}

impl<K> HashSet<K> {
    /// Returns the set's cardinality.
    pub fn len(&self) -> u32 {
        *self.len.get()
    }
    /// Returns `true` if the set contains no elements.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

pub enum SetError {
    // The member already exists in the target set
    Exists,
    // "[pdsl_core::HashSet::insert] Error: failed to find a valid entry
    // Out of storage space...
    Internal,
}

impl<K> HashSet<K>
where
    K: parity_codec::Codec + Hash + Eq,
{
    /// Adds a member into the set.
    ///
    /// Returns Ok(()) on success or `SetError::Exists` is if the element exists
    pub fn add(&mut self, key: K) -> Result<(), SetError> {
        match self.probe_inserting(&key) {
            Some(ProbeSlot::Occupied(_)) => Err(SetError::Exists),
            Some(ProbeSlot::Vacant(probe_index)) => {
                self.len.set(self.len() + 1);
                self.members.set(probe_index, key);
                Ok(())
            }
            None => Err(SetError::Internal),
        }
    }
}

impl<K> HashSet<K>
where
    K: parity_codec::Codec,
{
    /// The maximum amount of probing hops through the hash set.
    ///
    /// Look-ups into the hashtable will fail if no appropriate
    /// slot has been found after this amount of hops.
    const MAX_PROBE_HOPS: u32 = 32;

    /// Probes for a free or usable slot.
    ///
    /// # Note
    ///
    /// - Uses quadratic probing.
    /// - Returns `(true, _)` if there was a key-match of an already
    ///   occupied slot, returns `(false, _)` if the found slot is empty.
    /// - Returns `(_, n)` if `n` is the found probed index.
    fn probe<Q>(&self, key: &Q, inserting: bool) -> Option<ProbeSlot>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        // Convert the first 4 bytes in the keccak256 hash
        // of the key into a big-endian unsigned integer.
        let probe_start = bytes4_to_u32(
            slice_as_array4(&(hash::keccak256(key.borrow())[0..4])).expect(
                "[pdsl_core::HashSet::insert] Error \
                 couldn't convert to probe_start byte array",
            ),
        );
        // We need the hops counter to prevent theroretical endless loop situations.
        let mut probe_hops = 0;
        while probe_hops < Self::MAX_PROBE_HOPS {
            let probe_offset = probe_hops * probe_hops;
            let probe_index = probe_start.wrapping_add(probe_offset);
            match self.members.get(probe_index) {
                Some(key_) => {
                    if key == key_.borrow() {
                        // Keys match so we can return this probed slot.
                        return Some(ProbeSlot::Occupied(probe_index));
                    }
                }
                None => {
                    // Slot is free to use
                    if inserting {
                        return Some(ProbeSlot::Vacant(probe_index));
                    }
                }
            }
            probe_hops += 1;
        }
        None
    }

    /// Probes for a free or usable slot while inserting.
    ///
    /// Returns `None` if there is no mapping for the key.
    ///
    /// # Note
    ///
    /// For more information refer to the `fn probe` documentation.
    fn probe_inserting<Q>(&self, key: &Q) -> Option<ProbeSlot>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.probe(key, true)
    }

    /// Probes an occupied or once occupied slot with the given key.
    ///
    /// # Note
    ///
    /// For more information refer to the `fn probe` documentation.
    fn probe_inspecting<Q>(&self, key: &Q) -> Option<u32>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.probe(key, false).map(|slot| slot.index())
    }

    /// Removes a member from the set, returning its value if it exists.
    ///
    /// # Note
    ///
    /// The key may be any borrowed form of the sets's key type,
    /// but Hash and Eq on the borrowed form must match those for the key type.
    pub fn remove<Q>(&mut self, key: &Q) -> Option<K>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        let probe_index = self.probe_inspecting(key).expect(
            "[pdsl_core::HashSet::remove] Error: \
             failed at finding a valid entry",
        );
        if let Some(elem) = self.members.take(probe_index) {
            self.len.set(self.len() - 1);
            return Some(elem);
        }
        None
    }

    /// Returns `true` if the `key` is a member of the set.
    ///
    /// The key may be any borrowed form of the set's type,
    /// but Hash and Eq on the borrowed form must match those for the key type.
    pub fn contains<Q>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.get(key).is_some()
    }

    /// Returns an immutable reference to the value corresponding to the key.
    ///
    /// The key may be any borrowed form of the map's key type,
    /// but Hash and Eq on the borrowed form must match those for the key type.
    fn get<Q>(&self, key: &Q) -> Option<&K>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        if let Some(slot) = self.probe_inspecting(key) {
            return self.members.get(slot);
        }
        None
    }
}

impl<'a, K, Q: ?Sized> core::ops::Index<&'a Q> for HashSet<K>
where
    K: Eq + Hash + Borrow<Q> + parity_codec::Codec,
    Q: Eq + Hash,
{
    type Output = K;

    fn index(&self, index: &Q) -> &Self::Output {
        self.get(index).expect(
            "[pdsl_core::HashSet::index] Error: \
             expected `index` to be within bounds",
        )
    }
}

//
// Duplicate utility functions
//

/// The result of a slot probe.
pub(crate) enum ProbeSlot {
    /// The probed slot is empty or removed.
    Vacant(u32),
    /// The probed slot is occupied.
    Occupied(u32),
}

impl ProbeSlot {
    /// Returns the index of the probe slot.
    pub(crate) fn index(&self) -> u32 {
        match self {
            ProbeSlot::Vacant(index) | ProbeSlot::Occupied(index) => *index,
        }
    }
}

/// Converts the given bytes into a `u32` value.
///
/// The first byte in the array will be the most significant byte.
fn bytes4_to_u32(bytes: [u8; 4]) -> u32 {
    let mut res = 0;
    res |= (bytes[0] as u32) << 24;
    res |= (bytes[1] as u32) << 16;
    res |= (bytes[2] as u32) << 8;
    res |= (bytes[3] as u32) << 0;
    res
}

/// Converts the given slice into an array with fixed size of 4.
///
/// Returns `None` if the slice's length is not 4.
fn slice_as_array4<T>(bytes: &[T]) -> Option<[T; 4]>
where
    T: Default + Copy,
{
    if bytes.len() != 4 {
        return None;
    }
    let mut array = [T::default(); 4];
    for i in 0..4 {
        array[i] = bytes[i];
    }
    Some(array)
}
