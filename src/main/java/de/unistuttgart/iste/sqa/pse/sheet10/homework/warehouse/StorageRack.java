package de.unistuttgart.iste.sqa.pse.sheet10.homework.warehouse;

import de.unistuttgart.iste.sqa.pse.sheet10.homework.warehouse.items.StationeryItem;
import java.util.Optional;
import java.util.HashMap;
import java.util.Map;

/**
 * Represents a warehouse that can hold a fixed number of items.
 * The number of holdable items is defined by the capacity of the storage rack.
 *
 * @author Marvin Spiegel, Ismail Ratni
 */
public final class StorageRack {
	// @ private instance invariant capacity > 0;
	// @ private instance invariant numberOfItems >= 0;
	// @ private instance invariant numberOfItems <= capacity;

	private final int capacity;
	private int numberOfItems;
	private Optional<StationeryItem>[] items; //Array of Optional<StationeryItem> because we want to be able to store null values
											  // and array because we want to be able to access the items by index and fixed size
	private Map<Identifier, Integer> identifierToCompartmentMap;

	/*@
	@ requires capacity > 0;
	@ requires capacity < Integer.MAX_VALUE;
	@ ensures this.capacity == capacity;
	@ ensures numberOfItems == 0;
	@ ensures items != null;
	@ ensures (\forall int i; 0 <= i && i < capacity; items[i] == Optional.empty());
	@*/
	/**
	 * Creates a new storage rack with the given capacity.
	 *
	 * @param capacity capacity of the storage rack.
	 *
	 * @throws IllegalArgumentException If capacity is less than 1.
	 */
	public StorageRack(final int capacity) {
		if (capacity <= 0) {
			throw new IllegalArgumentException("A warehouse must have a minimum capacity of 1.");
		}
		this.capacity = capacity;
		numberOfItems = 0;

		// Initialize data structures
		items = new Optional[capacity];
		identifierToCompartmentMap = new HashMap<>();

		for (int i = 0; i < capacity; i++) {
			items[i] = Optional.empty();
		}
	}

	/*@
	@ requires stationeryItem != null;
	@ requires numberOfItems < capacity;
	@ ensures numberOfItems == \old(numberOfItems) + 1;
	 */
	/**
	 * Adds a new item to the storage rack.
	 *
	 * @param stationeryItem The item to add.
	 *
	 * @throws IllegalArgumentException If there is no empty compartment.
	 */
	public void addItem(final StationeryItem stationeryItem, final Identifier identifier) {
		assert stationeryItem != null : "stationeryItem must not be null";
		assert identifier != null : "identifier must not be null";
		int firstEmptyCompartment = findFirstEmptyCompartment();

		// Check if there is an available compartment
		if (firstEmptyCompartment != -1) {
			items[firstEmptyCompartment] = Optional.of(stationeryItem);
			identifierToCompartmentMap.put(identifier, firstEmptyCompartment);
			numberOfItems++;
		} else {
			// Handle the case where there are no available compartments using an exception
			throw new IllegalArgumentException("No available compartments. Cannot add item.");
		}
	}

	/*@
	  @ ensures numberOfItems == \old(numberOfItems) + 1;
	 @*/
	/**
	 * Finds the first empty compartment in the storage rack.
	 * @return The index of the first empty compartment or -1 if there is no empty compartment.
	 */
	private int findFirstEmptyCompartment() {
		for (int i = 0; i < capacity; i++) {
			if (!items[i].isPresent()) {
				return i;
			}
		}
		return -1;
	}

	/*@
	@ requires compartmentNumber >= 0 && compartmentNumber < capacity;
	@ ensures numberOfItems == \old(numberOfItems) - 1;
	@*/
	/**
	 * Removes the item from the given compartment.
	 * @param compartmentNumber The number of the compartment to remove the item from.
	 */
	public void removeItem(final int compartmentNumber) {
		assert compartmentNumber >= 0 && compartmentNumber < capacity : "Invalid compartment number";

		// Check if the compartment contains an item
		if (items[compartmentNumber].isPresent()) {
			Identifier removedIdentifier = getIdentifierForCompartment(compartmentNumber);
			items[compartmentNumber] = Optional.empty();
			identifierToCompartmentMap.remove(removedIdentifier);
			numberOfItems--;
		}
	}

	/*@
	@ requires compartmentNumber >= 0 && compartmentNumber < capacity;
	@ ensures \result != null;
	 */
	/**
	 * Returns the identifier for the given compartment.
	 * @param compartmentNumber The number of the compartment to get the identifier from.
	 * @throws IllegalArgumentException If there is no mapping for the specified compartment.
	 */
	private Identifier getIdentifierForCompartment(int compartmentNumber) {
		for (Map.Entry<Identifier, Integer> entry : identifierToCompartmentMap.entrySet()) {
			if (entry.getValue() == compartmentNumber) {
				return entry.getKey();
			}
		}
		throw new IllegalArgumentException("No mapping found for the specified compartment.");
	}


	/*@
	@ requires compartmentNumber >= 0 && compartmentNumber < capacity;
	@ ensures \result != null;
	@*/
	/**
	 * Returns the item in the given compartment.
	 * @param compartmentNumber The number of the compartment to get the item from.
	 */
	public /*@ pure @*/ Optional<StationeryItem> getItem(final int compartmentNumber) {
		assert compartmentNumber >= 0 && compartmentNumber < capacity : "Invalid compartment number";

		// Return the item in the specified compartment, if present
		return items[compartmentNumber];
	}

	/*@
	@ requires identifier != null;
	@ ensures \result != null;
	@*/
	/**
	 * Returns the compartment number for the given identifier.
	 * @param identifier The identifier to get the compartment number for.
	 */
	public /*@ pure @*/ Optional<Integer> getCompartmentNumberOf(final Identifier identifier) {
		assert identifier != null : "identifier must not be null";

		if (identifierToCompartmentMap.containsKey(identifier)) {
			return Optional.of(identifierToCompartmentMap.get(identifier));
		} else {
			return Optional.empty();
		}
	}

	/*@
	@ ensures \result == capacity;
	@*/
	/**
	 * @return The capacity of this warehouse in items.
	 */
	public /*@ pure @*/ int getCapacity() {
		return capacity;
	}

	/*@
	@ ensures \result == numberOfItems;
	@*/
	/**
	 * @return The number of items in this warehouse.
	 */
	public /*@ pure @*/ int getNumberOfItems() {
		return this.numberOfItems;
	}
}
