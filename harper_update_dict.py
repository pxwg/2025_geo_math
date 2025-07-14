import os
import shutil
import sys


def update_harper_dict(file_paths):
    target_dir = "./.harper_dict/"
    os.makedirs(target_dir, exist_ok=True)

    for file_path in file_paths:
        file_path_converted = file_path.replace("/", "%")
        file_name = file_path_converted.split("%geo_topo_2025%")[-1]
        target_file = f".%{file_name}"
        target_path = os.path.join(target_dir, target_file)

        try:
            shutil.copy(file_path, target_path)
            print(f"File {file_name} successfully updated to {target_path}")
        except FileNotFoundError:
            print(
                f"File {file_path} not found. Please check the file path and try again."
            )
        except Exception as e:
            print(f"Error occurred while copying the file {file_name}: {e}")


def update_from_local_dir():
    local_dir = "./.harper_dict_local/"
    if not os.path.exists(local_dir):
        print(f"Local directory {local_dir} does not exist.")
        return

    file_names = os.listdir(local_dir)
    file_paths = [os.path.join(local_dir, file_name) for file_name in file_names]
    update_harper_dict(file_paths)


if __name__ == "__main__":
    if len(sys.argv) > 1:
        file_paths = sys.argv[1:]
        update_harper_dict(file_paths)
    else:
        update_from_local_dir()
