package de.unistuttgart.iste.sqa.pse.sheet10.homework.warehouse;

import de.unistuttgart.iste.sqa.pse.sheet10.homework.warehouse.items.Compass;
import de.unistuttgart.iste.sqa.pse.sheet10.homework.warehouse.items.Pen;
import de.unistuttgart.iste.sqa.pse.sheet10.homework.warehouse.items.Ruler;
import de.unistuttgart.iste.sqa.pse.sheet10.homework.warehouse.items.StationeryItem;
import java.util.Optional;
import java.util.Random;
import java.util.HashSet;
import java.util.Set;

/**
 * Represents a company.
 *
 * A company stores items and processes orders.
 *
 * @author Marvin Spiegel, Ismail Ratni
 */
public final class Company {

	private final StorageRack itemStorageRack;
	private final Set<Customer> knownCustomers;
	private final Buffer orderBuffer;

	/*@
	@ ensures itemStorageRack != null;
	@ ensures orderBuffer != null;
	@ ensures knownCustomers != null;
	@*/
	/**
	 * Creates a new company.
	 * The company has a storage rack for items, a buffer for orders and a set of known customers.
	 */
	public Company() {
		orderBuffer = new Buffer();
		itemStorageRack = new StorageRack(75);
		knownCustomers = new HashSet<>();
	}
	/*@
	@ requires stationeryItem != null;
	@ ensures itemStorageRack.getItem(identifier).isPresent();
	 */

	/**
	 * Stores an item in the storage rack.
	 * @param stationeryItem
	 */
	public void storeInStorageRack(final StationeryItem stationeryItem) {
		try {
			Identifier identifier = new Identifier();
			itemStorageRack.addItem(stationeryItem, identifier);
			System.out.println("Item stored in the storage rack.");
		} catch (IllegalArgumentException e) {
			System.out.println("Item could not be stored in the storage rack. It may be full.");
		}
	}



	/*@
	@ requires identifier != null;
	@ requires customer != null;
	@ ensures orderBuffer.getItem(identifier).isPresent();
	@ ensures knownCustomers.contains(customer);
	@*/
	/**
	 * Processes an incoming order.
	 * @param identifier the identifier of the item
	 * @param customer the customer who ordered the item
	 */
	public void processIncomingOrder(final Identifier identifier, final Customer customer) {
		Optional<Integer> compartmentNumber = itemStorageRack.getCompartmentNumberOf(identifier);

		if (compartmentNumber.isPresent()) {
			StationeryItem orderedItem = itemStorageRack.getItem(compartmentNumber.get()).orElse(null);

			if (orderedItem != null) {
				itemStorageRack.removeItem(compartmentNumber.get());

				// Check if the customer is a new customer
				if (!knownCustomers.contains(customer)) {
					StationeryItem bonusItem = getBonusItem();
					orderBuffer.bufferItem(bonusItem);
					knownCustomers.add(customer);
					System.out.println("New customer! Bonus item added to the order buffer.");
				}

				orderBuffer.bufferItem(orderedItem);
				System.out.println("Item with identifier " + identifier + " added to the order buffer.");
			} else {
				System.out.println("Item with identifier " + identifier + " not found in storage rack. Order ignored.");
			}
		} else {
			System.out.println("Item with identifier " + identifier + " not found in storage rack. Order ignored.");
		}
	}

	/*@
	@ ensures \result != null;
	@ ensures \result.getIdentification().getType() == ItemType.PRESENT;
	@*/
	/**
	 * Generates a bonus item for marketing reasons.
	 *
	 * @return A marketing bonus item.
	 */
	private /*@ pure @*/ StationeryItem getBonusItem() {

		switch ((new Random().nextInt(3))) {
			case 1:
				return new Compass(new Identifier(), "A marketing bonus item.");
			case 2:
				return new Ruler(new Identifier(), "A marketing bonus item.");
			default:
				return new Pen(new Identifier(), "A marketing bonus item.");
		}
	}

	/**
	 * If items are waiting for packaging, takes the next available item from the buffer and return it.
	 *
	 * @return Optional next available item for packaging, or an empty Optional if there is none.
	 */
	public Optional<StationeryItem> takeItemForPackaging() {
		if (orderBuffer.isEmpty()) {
			return Optional.empty();
		} else {
			return Optional.of(orderBuffer.releaseItem());
		}
	}
}
